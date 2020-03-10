%{
#include "expr/emptybag.h"
%}

%rename(equals) CVC4::EmptyBag::operator==(const EmptyBag&) const;
%ignore CVC4::EmptyBag::operator!=(const EmptyBag&) const;

%rename(less) CVC4::EmptyBag::operator<(const EmptyBag&) const;
%rename(lessEqual) CVC4::EmptyBag::operator<=(const EmptyBag&) const;
%rename(greater) CVC4::EmptyBag::operator>(const EmptyBag&) const;
%rename(greaterEqual) CVC4::EmptyBag::operator>=(const EmptyBag&) const;

%rename(apply) CVC4::EmptyBagHashFunction::operator()(const EmptyBag&) const;

%ignore CVC4::operator<<(std::ostream& out, const EmptyBag& es);

%include "expr/emptybag.h"

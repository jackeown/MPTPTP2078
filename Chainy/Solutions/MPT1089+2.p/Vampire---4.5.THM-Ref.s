%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1089+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   32 (  54 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 182 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1987,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1887,f1891,f1895,f1899,f1980])).

fof(f1980,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_4 ),
    inference(avatar_contradiction_clause,[],[f1979])).

fof(f1979,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f1978,f1898])).

fof(f1898,plain,
    ( v1_relat_1(sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f1897])).

fof(f1897,plain,
    ( spl13_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f1978,plain,
    ( ~ v1_relat_1(sK1)
    | spl13_1
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f1977,f1894])).

fof(f1894,plain,
    ( v1_funct_1(sK1)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f1893])).

fof(f1893,plain,
    ( spl13_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f1977,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl13_1
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f1972,f1890])).

fof(f1890,plain,
    ( v1_finset_1(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f1889])).

fof(f1889,plain,
    ( spl13_2
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1972,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl13_1 ),
    inference(resolution,[],[f1866,f1886])).

fof(f1886,plain,
    ( ~ v1_finset_1(k9_relat_1(sK1,sK0))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f1885])).

fof(f1885,plain,
    ( spl13_1
  <=> v1_finset_1(k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f1866,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1775])).

fof(f1775,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1774])).

fof(f1774,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1713])).

fof(f1713,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

fof(f1899,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f1812,f1897])).

fof(f1812,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1786])).

fof(f1786,plain,
    ( ~ v1_finset_1(k9_relat_1(sK1,sK0))
    & v1_finset_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1728,f1785])).

fof(f1785,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k9_relat_1(X1,X0))
        & v1_finset_1(X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(k9_relat_1(sK1,sK0))
      & v1_finset_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1728,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k9_relat_1(X1,X0))
      & v1_finset_1(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1727])).

fof(f1727,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k9_relat_1(X1,X0))
      & v1_finset_1(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1721])).

fof(f1721,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v1_finset_1(X0)
         => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1720])).

fof(f1720,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_finset_1(X0)
       => v1_finset_1(k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_finset_1)).

fof(f1895,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f1813,f1893])).

fof(f1813,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1786])).

fof(f1891,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f1814,f1889])).

fof(f1814,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f1786])).

fof(f1887,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f1815,f1885])).

fof(f1815,plain,(
    ~ v1_finset_1(k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f1786])).
%------------------------------------------------------------------------------

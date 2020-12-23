%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1088+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   26 (  35 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  68 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1767,f1771,f1781,f1786])).

fof(f1786,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f1785])).

fof(f1785,plain,
    ( $false
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f1783,f1770])).

% (11252)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
fof(f1770,plain,
    ( v1_finset_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f1769])).

fof(f1769,plain,
    ( spl3_2
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1783,plain,
    ( ~ v1_finset_1(sK0)
    | spl3_4 ),
    inference(resolution,[],[f1780,f1762])).

fof(f1762,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k4_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f1746])).

fof(f1746,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k4_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1712])).

fof(f1712,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_finset_1)).

fof(f1780,plain,
    ( ~ v1_finset_1(k4_xboole_0(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f1779,plain,
    ( spl3_4
  <=> v1_finset_1(k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1781,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f1776,f1765,f1779])).

fof(f1765,plain,
    ( spl3_1
  <=> v1_finset_1(k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1776,plain,
    ( ~ v1_finset_1(k4_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(backward_demodulation,[],[f1766,f1754])).

fof(f1754,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f1766,plain,
    ( ~ v1_finset_1(k6_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f1765])).

fof(f1771,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f1752,f1769])).

fof(f1752,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f1749])).

fof(f1749,plain,
    ( ~ v1_finset_1(k6_subset_1(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1738,f1748])).

fof(f1748,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k6_subset_1(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k6_subset_1(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1738,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k6_subset_1(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1719])).

fof(f1719,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k6_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1718])).

fof(f1718,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_finset_1)).

fof(f1767,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f1753,f1765])).

fof(f1753,plain,(
    ~ v1_finset_1(k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1749])).
%------------------------------------------------------------------------------

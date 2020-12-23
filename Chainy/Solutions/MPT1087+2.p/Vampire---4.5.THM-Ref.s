%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1087+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  27 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  54 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (31805)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% (31806)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% (31811)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (31799)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
fof(f1860,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1826,f1830,f1852])).

fof(f1852,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f1851])).

fof(f1851,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1847,f1829])).

fof(f1829,plain,
    ( v1_finset_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f1828])).

fof(f1828,plain,
    ( spl5_2
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1847,plain,
    ( ~ v1_finset_1(sK0)
    | spl5_1 ),
    inference(resolution,[],[f1818,f1825])).

fof(f1825,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f1824])).

fof(f1824,plain,
    ( spl5_1
  <=> v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1818,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f1755])).

fof(f1755,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1711])).

fof(f1711,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_finset_1)).

fof(f1830,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f1768,f1828])).

fof(f1768,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f1758])).

fof(f1758,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1722,f1757])).

fof(f1757,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k3_xboole_0(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1722,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k3_xboole_0(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1717])).

fof(f1717,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1716])).

fof(f1716,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).

fof(f1826,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f1769,f1824])).

fof(f1769,plain,(
    ~ v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1758])).
%------------------------------------------------------------------------------

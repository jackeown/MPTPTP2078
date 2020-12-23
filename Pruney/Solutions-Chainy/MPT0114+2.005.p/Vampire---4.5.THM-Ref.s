%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:47 EST 2020

% Result     : Theorem 2.79s
% Output     : Refutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 111 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 289 expanded)
%              Number of equality atoms :   10 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3775,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f139,f140,f1780,f1874,f3774])).

fof(f3774,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f3773])).

fof(f3773,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f3772,f132])).

fof(f132,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f3772,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f3771,f121])).

fof(f121,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f91,f84])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f3771,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f3759,f90])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f3759,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k4_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2))))
    | spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f2096,f122])).

fof(f122,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f92,f84])).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f2096,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0))
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f1875,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1875,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f136,f129,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f129,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f136,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1874,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1873])).

fof(f1873,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f1872,f128])).

fof(f128,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1872,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1860,f90])).

fof(f1860,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | spl3_2 ),
    inference(superposition,[],[f1784,f122])).

fof(f1784,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),X0))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f133,f103])).

fof(f133,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1780,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f1779])).

fof(f1779,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f1778,f128])).

fof(f1778,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(forward_demodulation,[],[f1773,f90])).

fof(f1773,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | spl3_3 ),
    inference(superposition,[],[f1422,f122])).

fof(f1422,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f137,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f140,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f64,f131,f127])).

fof(f64,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f59,f60])).

fof(f60,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f42])).

fof(f42,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f139,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f113,f135,f127])).

fof(f113,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f65,f84])).

fof(f65,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f138,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f112,f135,f131,f127])).

fof(f112,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f66,f84])).

fof(f66,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (24489)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.44  % (24473)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.47  % (24486)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.48  % (24478)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.49  % (24494)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (24480)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (24485)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (24496)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (24484)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (24490)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (24479)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (24498)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (24493)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (24476)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (24488)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (24477)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (24482)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (24474)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (24497)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (24492)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (24495)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (24501)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (24500)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (24481)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (24499)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (24487)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (24475)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (24491)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (24472)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (24483)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.79/0.77  % (24498)Refutation found. Thanks to Tanya!
% 2.79/0.77  % SZS status Theorem for theBenchmark
% 2.79/0.77  % SZS output start Proof for theBenchmark
% 2.79/0.77  fof(f3775,plain,(
% 2.79/0.77    $false),
% 2.79/0.77    inference(avatar_sat_refutation,[],[f138,f139,f140,f1780,f1874,f3774])).
% 2.79/0.77  fof(f3774,plain,(
% 2.79/0.77    spl3_1 | ~spl3_2 | ~spl3_3),
% 2.79/0.77    inference(avatar_contradiction_clause,[],[f3773])).
% 2.79/0.77  fof(f3773,plain,(
% 2.79/0.77    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 2.79/0.77    inference(subsumption_resolution,[],[f3772,f132])).
% 2.79/0.77  fof(f132,plain,(
% 2.79/0.77    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 2.79/0.77    inference(avatar_component_clause,[],[f131])).
% 2.79/0.77  fof(f131,plain,(
% 2.79/0.77    spl3_2 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.79/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.79/0.77  fof(f3772,plain,(
% 2.79/0.77    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | (spl3_1 | ~spl3_3)),
% 2.79/0.77    inference(forward_demodulation,[],[f3771,f121])).
% 2.79/0.77  fof(f121,plain,(
% 2.79/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.79/0.77    inference(definition_unfolding,[],[f91,f84])).
% 2.79/0.77  fof(f84,plain,(
% 2.79/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.79/0.77    inference(cnf_transformation,[],[f22])).
% 2.79/0.77  fof(f22,axiom,(
% 2.79/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.79/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.79/0.77  fof(f91,plain,(
% 2.79/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.79/0.77    inference(cnf_transformation,[],[f38])).
% 2.79/0.77  fof(f38,axiom,(
% 2.79/0.77    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.79/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.79/0.77  fof(f3771,plain,(
% 2.79/0.77    ~r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | (spl3_1 | ~spl3_3)),
% 2.79/0.77    inference(forward_demodulation,[],[f3759,f90])).
% 2.79/0.77  fof(f90,plain,(
% 2.79/0.77    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.79/0.77    inference(cnf_transformation,[],[f3])).
% 2.79/0.77  fof(f3,axiom,(
% 2.79/0.77    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.79/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.79/0.77  fof(f3759,plain,(
% 2.79/0.77    ~r1_tarski(sK0,k2_xboole_0(k4_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2)))) | (spl3_1 | ~spl3_3)),
% 2.79/0.77    inference(superposition,[],[f2096,f122])).
% 2.79/0.77  fof(f122,plain,(
% 2.79/0.77    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.79/0.77    inference(definition_unfolding,[],[f92,f84])).
% 2.79/0.77  fof(f92,plain,(
% 2.79/0.77    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.79/0.77    inference(cnf_transformation,[],[f26])).
% 2.79/0.77  fof(f26,axiom,(
% 2.79/0.77    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.79/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 2.79/0.77  fof(f2096,plain,(
% 2.79/0.77    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(k2_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0))) ) | (spl3_1 | ~spl3_3)),
% 2.79/0.77    inference(unit_resulting_resolution,[],[f1875,f103])).
% 2.79/0.77  fof(f103,plain,(
% 2.79/0.77    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.79/0.77    inference(cnf_transformation,[],[f47])).
% 2.79/0.77  fof(f47,plain,(
% 2.79/0.77    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.79/0.77    inference(ennf_transformation,[],[f9])).
% 2.79/0.77  fof(f9,axiom,(
% 2.79/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.79/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.79/0.77  fof(f1875,plain,(
% 2.79/0.77    ~r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | (spl3_1 | ~spl3_3)),
% 2.79/0.77    inference(unit_resulting_resolution,[],[f136,f129,f108])).
% 2.79/0.77  fof(f108,plain,(
% 2.79/0.77    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.79/0.77    inference(cnf_transformation,[],[f54])).
% 2.79/0.77  fof(f54,plain,(
% 2.79/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.79/0.77    inference(flattening,[],[f53])).
% 2.79/0.77  fof(f53,plain,(
% 2.79/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.79/0.77    inference(ennf_transformation,[],[f31])).
% 2.79/0.77  fof(f31,axiom,(
% 2.79/0.77    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.79/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 2.79/0.77  fof(f129,plain,(
% 2.79/0.77    ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | spl3_1),
% 2.79/0.77    inference(avatar_component_clause,[],[f127])).
% 2.79/0.77  fof(f127,plain,(
% 2.79/0.77    spl3_1 <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.79/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.79/0.77  fof(f136,plain,(
% 2.79/0.77    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 2.79/0.77    inference(avatar_component_clause,[],[f135])).
% 2.79/0.77  fof(f135,plain,(
% 2.79/0.77    spl3_3 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 2.79/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.79/0.77  fof(f1874,plain,(
% 2.79/0.77    ~spl3_1 | spl3_2),
% 2.79/0.77    inference(avatar_contradiction_clause,[],[f1873])).
% 2.79/0.77  fof(f1873,plain,(
% 2.79/0.77    $false | (~spl3_1 | spl3_2)),
% 2.79/0.77    inference(subsumption_resolution,[],[f1872,f128])).
% 2.79/0.77  fof(f128,plain,(
% 2.79/0.77    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_1),
% 2.79/0.77    inference(avatar_component_clause,[],[f127])).
% 2.79/0.78  fof(f1872,plain,(
% 2.79/0.78    ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | spl3_2),
% 2.79/0.78    inference(forward_demodulation,[],[f1860,f90])).
% 2.79/0.78  fof(f1860,plain,(
% 2.79/0.78    ~r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | spl3_2),
% 2.79/0.78    inference(superposition,[],[f1784,f122])).
% 2.79/0.78  fof(f1784,plain,(
% 2.79/0.78    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),X0))) ) | spl3_2),
% 2.79/0.78    inference(unit_resulting_resolution,[],[f133,f103])).
% 2.79/0.78  fof(f133,plain,(
% 2.79/0.78    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 2.79/0.78    inference(avatar_component_clause,[],[f131])).
% 2.79/0.78  fof(f1780,plain,(
% 2.79/0.78    ~spl3_1 | spl3_3),
% 2.79/0.78    inference(avatar_contradiction_clause,[],[f1779])).
% 2.79/0.78  fof(f1779,plain,(
% 2.79/0.78    $false | (~spl3_1 | spl3_3)),
% 2.79/0.78    inference(subsumption_resolution,[],[f1778,f128])).
% 2.79/0.78  fof(f1778,plain,(
% 2.79/0.78    ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | spl3_3),
% 2.79/0.78    inference(forward_demodulation,[],[f1773,f90])).
% 2.79/0.78  fof(f1773,plain,(
% 2.79/0.78    ~r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) | spl3_3),
% 2.79/0.78    inference(superposition,[],[f1422,f122])).
% 2.79/0.78  fof(f1422,plain,(
% 2.79/0.78    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ) | spl3_3),
% 2.79/0.78    inference(unit_resulting_resolution,[],[f137,f104])).
% 2.79/0.78  fof(f104,plain,(
% 2.79/0.78    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.79/0.78    inference(cnf_transformation,[],[f47])).
% 2.79/0.78  fof(f137,plain,(
% 2.79/0.78    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_3),
% 2.79/0.78    inference(avatar_component_clause,[],[f135])).
% 2.79/0.78  fof(f140,plain,(
% 2.79/0.78    spl3_1 | spl3_2),
% 2.79/0.78    inference(avatar_split_clause,[],[f64,f131,f127])).
% 2.79/0.78  fof(f64,plain,(
% 2.79/0.78    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.79/0.78    inference(cnf_transformation,[],[f61])).
% 2.79/0.78  fof(f61,plain,(
% 2.79/0.78    (~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2)))),
% 2.79/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f59,f60])).
% 2.79/0.78  fof(f60,plain,(
% 2.79/0.78    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)))) => ((~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))))),
% 2.79/0.78    introduced(choice_axiom,[])).
% 2.79/0.78  fof(f59,plain,(
% 2.79/0.78    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 2.79/0.78    inference(flattening,[],[f58])).
% 2.79/0.78  fof(f58,plain,(
% 2.79/0.78    ? [X0,X1,X2] : (((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 2.79/0.78    inference(nnf_transformation,[],[f46])).
% 2.79/0.78  fof(f46,plain,(
% 2.79/0.78    ? [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <~> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.79/0.78    inference(ennf_transformation,[],[f43])).
% 2.79/0.78  fof(f43,negated_conjecture,(
% 2.79/0.78    ~! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.79/0.78    inference(negated_conjecture,[],[f42])).
% 2.79/0.78  fof(f42,conjecture,(
% 2.79/0.78    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.79/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 2.79/0.78  fof(f139,plain,(
% 2.79/0.78    spl3_1 | spl3_3),
% 2.79/0.78    inference(avatar_split_clause,[],[f113,f135,f127])).
% 2.79/0.78  fof(f113,plain,(
% 2.79/0.78    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.79/0.78    inference(definition_unfolding,[],[f65,f84])).
% 2.79/0.78  fof(f65,plain,(
% 2.79/0.78    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.79/0.78    inference(cnf_transformation,[],[f61])).
% 2.79/0.78  fof(f138,plain,(
% 2.79/0.78    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 2.79/0.78    inference(avatar_split_clause,[],[f112,f135,f131,f127])).
% 2.79/0.78  fof(f112,plain,(
% 2.79/0.78    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.79/0.78    inference(definition_unfolding,[],[f66,f84])).
% 2.79/0.78  fof(f66,plain,(
% 2.79/0.78    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.79/0.78    inference(cnf_transformation,[],[f61])).
% 2.79/0.78  % SZS output end Proof for theBenchmark
% 2.79/0.78  % (24498)------------------------------
% 2.79/0.78  % (24498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.79/0.78  % (24498)Termination reason: Refutation
% 2.79/0.78  
% 2.79/0.78  % (24498)Memory used [KB]: 12792
% 2.79/0.78  % (24498)Time elapsed: 0.339 s
% 2.79/0.78  % (24498)------------------------------
% 2.79/0.78  % (24498)------------------------------
% 2.79/0.78  % (24471)Success in time 0.419 s
%------------------------------------------------------------------------------

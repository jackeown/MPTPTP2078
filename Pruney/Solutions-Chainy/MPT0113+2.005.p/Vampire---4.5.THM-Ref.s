%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:33 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 101 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :  137 ( 197 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2434,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f85,f272,f2399,f2431,f2433])).

fof(f2433,plain,
    ( spl5_1
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f2432])).

fof(f2432,plain,
    ( $false
    | spl5_1
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f2417,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2417,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1)
    | spl5_1
    | ~ spl5_25 ),
    inference(superposition,[],[f138,f2398])).

fof(f2398,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f2396])).

fof(f2396,plain,
    ( spl5_25
  <=> k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f138,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f65,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2431,plain,
    ( spl5_4
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f2430])).

fof(f2430,plain,
    ( $false
    | spl5_4
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f2416,f89])).

fof(f89,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f59,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f2416,plain,
    ( ~ r1_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | spl5_4
    | ~ spl5_25 ),
    inference(superposition,[],[f1360,f2398])).

fof(f1360,plain,
    ( ! [X0] : ~ r1_xboole_0(sK2,k2_xboole_0(sK0,X0))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f84,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f84,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_4
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2399,plain,
    ( spl5_25
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f845,f269,f2396])).

fof(f269,plain,
    ( spl5_8
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f845,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f803,f834])).

fof(f834,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0))
    | ~ spl5_8 ),
    inference(superposition,[],[f170,f271])).

fof(f271,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f269])).

fof(f170,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[],[f61,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f803,plain,
    ( k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0))
    | ~ spl5_8 ),
    inference(superposition,[],[f164,f271])).

fof(f164,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f60,f41])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f272,plain,
    ( spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f100,f72,f269])).

fof(f72,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f100,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f74,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f74,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f85,plain,
    ( ~ spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f76,f67,f82])).

fof(f67,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f76,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f69,f49])).

fof(f69,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f75,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f56,f72])).

fof(f56,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f34,f43])).

fof(f34,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f70,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f35,f67,f63])).

fof(f35,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:39:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (18296)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (18293)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (18297)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (18306)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (18305)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (18298)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (18292)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (18295)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (18294)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (18301)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.54  % (18303)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.55  % (18308)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.55  % (18299)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.55  % (18302)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.55  % (18300)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.56  % (18304)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.49/0.56  % (18291)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.49/0.57  % (18307)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.75/0.62  % (18306)Refutation found. Thanks to Tanya!
% 1.75/0.62  % SZS status Theorem for theBenchmark
% 1.75/0.62  % SZS output start Proof for theBenchmark
% 1.75/0.62  fof(f2434,plain,(
% 1.75/0.62    $false),
% 1.75/0.62    inference(avatar_sat_refutation,[],[f70,f75,f85,f272,f2399,f2431,f2433])).
% 1.75/0.62  fof(f2433,plain,(
% 1.75/0.62    spl5_1 | ~spl5_25),
% 1.75/0.62    inference(avatar_contradiction_clause,[],[f2432])).
% 1.75/0.62  fof(f2432,plain,(
% 1.75/0.62    $false | (spl5_1 | ~spl5_25)),
% 1.75/0.62    inference(subsumption_resolution,[],[f2417,f58])).
% 1.75/0.62  fof(f58,plain,(
% 1.75/0.62    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.75/0.62    inference(definition_unfolding,[],[f39,f43])).
% 1.75/0.62  fof(f43,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.75/0.62    inference(cnf_transformation,[],[f7])).
% 1.75/0.62  fof(f7,axiom,(
% 1.75/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.75/0.62  fof(f39,plain,(
% 1.75/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f10])).
% 1.75/0.62  fof(f10,axiom,(
% 1.75/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.75/0.62  fof(f2417,plain,(
% 1.75/0.62    ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK1) | (spl5_1 | ~spl5_25)),
% 1.75/0.62    inference(superposition,[],[f138,f2398])).
% 1.75/0.62  fof(f2398,plain,(
% 1.75/0.62    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl5_25),
% 1.75/0.62    inference(avatar_component_clause,[],[f2396])).
% 1.75/0.62  fof(f2396,plain,(
% 1.75/0.62    spl5_25 <=> k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.75/0.62  fof(f138,plain,(
% 1.75/0.62    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK1)) ) | spl5_1),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f65,f55])).
% 1.75/0.62  fof(f55,plain,(
% 1.75/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f26])).
% 1.75/0.62  fof(f26,plain,(
% 1.75/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.75/0.62    inference(ennf_transformation,[],[f8])).
% 1.75/0.62  fof(f8,axiom,(
% 1.75/0.62    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.75/0.62  fof(f65,plain,(
% 1.75/0.62    ~r1_tarski(sK0,sK1) | spl5_1),
% 1.75/0.62    inference(avatar_component_clause,[],[f63])).
% 1.75/0.62  fof(f63,plain,(
% 1.75/0.62    spl5_1 <=> r1_tarski(sK0,sK1)),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.75/0.62  fof(f2431,plain,(
% 1.75/0.62    spl5_4 | ~spl5_25),
% 1.75/0.62    inference(avatar_contradiction_clause,[],[f2430])).
% 1.75/0.62  fof(f2430,plain,(
% 1.75/0.62    $false | (spl5_4 | ~spl5_25)),
% 1.75/0.62    inference(subsumption_resolution,[],[f2416,f89])).
% 1.75/0.62  fof(f89,plain,(
% 1.75/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f59,f49])).
% 1.75/0.62  fof(f49,plain,(
% 1.75/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f24])).
% 1.75/0.62  fof(f24,plain,(
% 1.75/0.62    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.75/0.62    inference(ennf_transformation,[],[f4])).
% 1.75/0.62  fof(f4,axiom,(
% 1.75/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.75/0.62  fof(f59,plain,(
% 1.75/0.62    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.75/0.62    inference(definition_unfolding,[],[f40,f43])).
% 1.75/0.62  fof(f40,plain,(
% 1.75/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f16])).
% 1.75/0.62  fof(f16,axiom,(
% 1.75/0.62    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.75/0.62  fof(f2416,plain,(
% 1.75/0.62    ~r1_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (spl5_4 | ~spl5_25)),
% 1.75/0.62    inference(superposition,[],[f1360,f2398])).
% 1.75/0.62  fof(f1360,plain,(
% 1.75/0.62    ( ! [X0] : (~r1_xboole_0(sK2,k2_xboole_0(sK0,X0))) ) | spl5_4),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f84,f53])).
% 1.75/0.62  fof(f53,plain,(
% 1.75/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f25])).
% 1.75/0.62  fof(f25,plain,(
% 1.75/0.62    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.75/0.62    inference(ennf_transformation,[],[f15])).
% 1.75/0.62  fof(f15,axiom,(
% 1.75/0.62    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.75/0.62  fof(f84,plain,(
% 1.75/0.62    ~r1_xboole_0(sK2,sK0) | spl5_4),
% 1.75/0.62    inference(avatar_component_clause,[],[f82])).
% 1.75/0.62  fof(f82,plain,(
% 1.75/0.62    spl5_4 <=> r1_xboole_0(sK2,sK0)),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.75/0.62  fof(f2399,plain,(
% 1.75/0.62    spl5_25 | ~spl5_8),
% 1.75/0.62    inference(avatar_split_clause,[],[f845,f269,f2396])).
% 1.75/0.62  fof(f269,plain,(
% 1.75/0.62    spl5_8 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.75/0.62  fof(f845,plain,(
% 1.75/0.62    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl5_8),
% 1.75/0.62    inference(backward_demodulation,[],[f803,f834])).
% 1.75/0.62  fof(f834,plain,(
% 1.75/0.62    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)) | ~spl5_8),
% 1.75/0.62    inference(superposition,[],[f170,f271])).
% 1.75/0.62  fof(f271,plain,(
% 1.75/0.62    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl5_8),
% 1.75/0.62    inference(avatar_component_clause,[],[f269])).
% 1.75/0.62  fof(f170,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,k3_xboole_0(X1,X0))) = X0) )),
% 1.75/0.62    inference(superposition,[],[f61,f41])).
% 1.75/0.62  fof(f41,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.75/0.62    inference(cnf_transformation,[],[f2])).
% 1.75/0.62  fof(f2,axiom,(
% 1.75/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.75/0.62  fof(f61,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.75/0.62    inference(definition_unfolding,[],[f45,f43])).
% 1.75/0.62  fof(f45,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.75/0.62    inference(cnf_transformation,[],[f13])).
% 1.75/0.62  fof(f13,axiom,(
% 1.75/0.62    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.75/0.62  fof(f803,plain,(
% 1.75/0.62    k2_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0)) | ~spl5_8),
% 1.75/0.62    inference(superposition,[],[f164,f271])).
% 1.75/0.62  fof(f164,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) )),
% 1.75/0.62    inference(superposition,[],[f60,f41])).
% 1.75/0.62  fof(f60,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.75/0.62    inference(definition_unfolding,[],[f44,f43])).
% 1.75/0.62  fof(f44,plain,(
% 1.75/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.75/0.62    inference(cnf_transformation,[],[f11])).
% 1.75/0.62  fof(f11,axiom,(
% 1.75/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.75/0.62  fof(f272,plain,(
% 1.75/0.62    spl5_8 | ~spl5_3),
% 1.75/0.62    inference(avatar_split_clause,[],[f100,f72,f269])).
% 1.75/0.62  fof(f72,plain,(
% 1.75/0.62    spl5_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.75/0.62  fof(f100,plain,(
% 1.75/0.62    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl5_3),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f74,f48])).
% 1.75/0.62  fof(f48,plain,(
% 1.75/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.75/0.62    inference(cnf_transformation,[],[f23])).
% 1.75/0.62  fof(f23,plain,(
% 1.75/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.75/0.62    inference(ennf_transformation,[],[f9])).
% 1.75/0.62  fof(f9,axiom,(
% 1.75/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.75/0.62  fof(f74,plain,(
% 1.75/0.62    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl5_3),
% 1.75/0.62    inference(avatar_component_clause,[],[f72])).
% 1.75/0.62  fof(f85,plain,(
% 1.75/0.62    ~spl5_4 | spl5_2),
% 1.75/0.62    inference(avatar_split_clause,[],[f76,f67,f82])).
% 1.75/0.62  fof(f67,plain,(
% 1.75/0.62    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 1.75/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.75/0.62  fof(f76,plain,(
% 1.75/0.62    ~r1_xboole_0(sK2,sK0) | spl5_2),
% 1.75/0.62    inference(unit_resulting_resolution,[],[f69,f49])).
% 1.75/0.62  fof(f69,plain,(
% 1.75/0.62    ~r1_xboole_0(sK0,sK2) | spl5_2),
% 1.75/0.62    inference(avatar_component_clause,[],[f67])).
% 1.75/0.62  fof(f75,plain,(
% 1.75/0.62    spl5_3),
% 1.75/0.62    inference(avatar_split_clause,[],[f56,f72])).
% 1.75/0.62  fof(f56,plain,(
% 1.75/0.62    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.75/0.62    inference(definition_unfolding,[],[f34,f43])).
% 1.75/0.62  fof(f34,plain,(
% 1.75/0.62    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.75/0.62    inference(cnf_transformation,[],[f28])).
% 1.75/0.62  fof(f28,plain,(
% 1.75/0.62    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.75/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f27])).
% 1.75/0.62  fof(f27,plain,(
% 1.75/0.62    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.75/0.62    introduced(choice_axiom,[])).
% 1.75/0.62  fof(f20,plain,(
% 1.75/0.62    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.75/0.62    inference(ennf_transformation,[],[f18])).
% 1.75/0.62  fof(f18,negated_conjecture,(
% 1.75/0.62    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.75/0.62    inference(negated_conjecture,[],[f17])).
% 1.75/0.62  fof(f17,conjecture,(
% 1.75/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.75/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.75/0.62  fof(f70,plain,(
% 1.75/0.62    ~spl5_1 | ~spl5_2),
% 1.75/0.62    inference(avatar_split_clause,[],[f35,f67,f63])).
% 1.75/0.62  fof(f35,plain,(
% 1.75/0.62    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.75/0.62    inference(cnf_transformation,[],[f28])).
% 1.75/0.62  % SZS output end Proof for theBenchmark
% 1.75/0.62  % (18306)------------------------------
% 1.75/0.62  % (18306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.62  % (18306)Termination reason: Refutation
% 1.75/0.62  
% 1.75/0.62  % (18306)Memory used [KB]: 12025
% 1.75/0.62  % (18306)Time elapsed: 0.126 s
% 1.75/0.62  % (18306)------------------------------
% 1.75/0.62  % (18306)------------------------------
% 1.75/0.63  % (18290)Success in time 0.263 s
%------------------------------------------------------------------------------

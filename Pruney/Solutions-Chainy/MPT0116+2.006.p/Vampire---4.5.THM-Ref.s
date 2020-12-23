%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 137 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :    6
%              Number of atoms          :  186 ( 299 expanded)
%              Number of equality atoms :   37 (  68 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f35,f39,f43,f47,f57,f61,f95,f136,f180,f203,f219,f232,f237,f379,f396,f398])).

fof(f398,plain,
    ( spl3_35
    | ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | spl3_35
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f378,f395])).

fof(f395,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl3_36
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f378,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK0)
    | spl3_35 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl3_35
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f396,plain,
    ( spl3_36
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f241,f235,f33,f394])).

fof(f33,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f235,plain,
    ( spl3_22
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f241,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(superposition,[],[f34,f236])).

fof(f236,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f235])).

fof(f34,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f379,plain,
    ( ~ spl3_35
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f256,f216,f93,f376])).

fof(f93,plain,
    ( spl3_12
  <=> ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f216,plain,
    ( spl3_20
  <=> sK0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f256,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK0)
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(superposition,[],[f94,f218])).

fof(f218,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f216])).

fof(f94,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f237,plain,
    ( spl3_22
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f233,f230,f201,f178,f55,f235])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f178,plain,
    ( spl3_17
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f201,plain,
    ( spl3_18
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f230,plain,
    ( spl3_21
  <=> ! [X1,X0] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f233,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f231,f210])).

fof(f210,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,X9)
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f209,f56])).

fof(f56,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f209,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k5_xboole_0(X8,k3_xboole_0(X8,X9))
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(superposition,[],[f202,f179])).

fof(f179,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f178])).

fof(f202,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f201])).

fof(f231,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f230])).

fof(f232,plain,
    ( spl3_21
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f78,f59,f230])).

fof(f59,plain,
    ( spl3_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f78,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_9 ),
    inference(superposition,[],[f60,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f219,plain,
    ( spl3_20
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f140,f134,f23,f216])).

fof(f23,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f134,plain,
    ( spl3_15
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f140,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f25,f135])).

fof(f135,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f25,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f203,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f76,f55,f37,f201])).

fof(f37,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f76,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f56,f38])).

fof(f38,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f180,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f63,f41,f33,f178])).

fof(f41,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f63,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f34,f42])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f136,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f64,f41,f37,f134])).

fof(f64,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f42,f38])).

fof(f95,plain,
    ( spl3_12
    | spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f69,f45,f28,f93])).

fof(f28,plain,
    ( spl3_2
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f69,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))
    | spl3_2
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f30,f46])).

fof(f46,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
        | r1_tarski(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f30,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f61,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f19,f59])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f18,f55])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f43,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f39,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f31,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f26,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f23])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (22174)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (22176)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (22170)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (22169)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (22172)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (22182)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (22171)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (22175)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (22177)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (22173)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (22180)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (22179)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (22183)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (22173)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f399,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f26,f31,f35,f39,f43,f47,f57,f61,f95,f136,f180,f203,f219,f232,f237,f379,f396,f398])).
% 0.21/0.49  fof(f398,plain,(
% 0.21/0.49    spl3_35 | ~spl3_36),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f397])).
% 0.21/0.49  fof(f397,plain,(
% 0.21/0.49    $false | (spl3_35 | ~spl3_36)),
% 0.21/0.49    inference(subsumption_resolution,[],[f378,f395])).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f394])).
% 0.21/0.49  fof(f394,plain,(
% 0.21/0.49    spl3_36 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    ~r1_tarski(k4_xboole_0(sK0,sK2),sK0) | spl3_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f376])).
% 0.21/0.49  fof(f376,plain,(
% 0.21/0.49    spl3_35 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.49  fof(f396,plain,(
% 0.21/0.49    spl3_36 | ~spl3_3 | ~spl3_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f241,f235,f33,f394])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl3_3 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    spl3_22 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | (~spl3_3 | ~spl3_22)),
% 0.21/0.49    inference(superposition,[],[f34,f236])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f235])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f33])).
% 0.21/0.49  fof(f379,plain,(
% 0.21/0.49    ~spl3_35 | ~spl3_12 | ~spl3_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f256,f216,f93,f376])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl3_12 <=> ! [X0] : ~r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    spl3_20 <=> sK0 = k3_xboole_0(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ~r1_tarski(k4_xboole_0(sK0,sK2),sK0) | (~spl3_12 | ~spl3_20)),
% 0.21/0.49    inference(superposition,[],[f94,f218])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    sK0 = k3_xboole_0(sK1,sK0) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f216])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) ) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    spl3_22 | ~spl3_8 | ~spl3_17 | ~spl3_18 | ~spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f233,f230,f201,f178,f55,f235])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_8 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    spl3_17 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl3_18 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    spl3_21 <=> ! [X1,X0] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) ) | (~spl3_8 | ~spl3_17 | ~spl3_18 | ~spl3_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f231,f210])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,X9)) ) | (~spl3_8 | ~spl3_17 | ~spl3_18)),
% 0.21/0.49    inference(forward_demodulation,[],[f209,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k5_xboole_0(X8,k3_xboole_0(X8,X9))) ) | (~spl3_17 | ~spl3_18)),
% 0.21/0.49    inference(superposition,[],[f202,f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f178])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f201])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f230])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    spl3_21 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f59,f230])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_9),
% 0.21/0.49    inference(superposition,[],[f60,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl3_20 | ~spl3_1 | ~spl3_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f140,f134,f23,f216])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl3_15 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    sK0 = k3_xboole_0(sK1,sK0) | (~spl3_1 | ~spl3_15)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f25,f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | ~spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f134])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f23])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    spl3_18 | ~spl3_4 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f76,f55,f37,f201])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | (~spl3_4 | ~spl3_8)),
% 0.21/0.49    inference(superposition,[],[f56,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f37])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl3_17 | ~spl3_3 | ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f41,f33,f178])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl3_5 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) ) | (~spl3_3 | ~spl3_5)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f34,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl3_15 | ~spl3_4 | ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f64,f41,f37,f134])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | (~spl3_4 | ~spl3_5)),
% 0.21/0.49    inference(superposition,[],[f42,f38])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl3_12 | spl3_2 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f69,f45,f28,f93])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    spl3_2 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl3_6 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) ) | (spl3_2 | ~spl3_6)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f30,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) ) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f28])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f59])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f55])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f45])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f41])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f33])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f28])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f23])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (22173)------------------------------
% 0.21/0.49  % (22173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22173)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (22173)Memory used [KB]: 6268
% 0.21/0.49  % (22173)Time elapsed: 0.088 s
% 0.21/0.49  % (22173)------------------------------
% 0.21/0.49  % (22173)------------------------------
% 0.21/0.50  % (22167)Success in time 0.135 s
%------------------------------------------------------------------------------

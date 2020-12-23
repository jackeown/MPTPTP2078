%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 (  95 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 229 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f63,f459,f470,f508])).

fof(f508,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f507,f466,f60,f45])).

fof(f45,plain,
    ( spl3_1
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f60,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f466,plain,
    ( spl3_9
  <=> k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f507,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f493,f78])).

fof(f78,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f493,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f128,f468])).

fof(f468,plain,
    ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f466])).

fof(f128,plain,
    ( ! [X2,X3] : k4_xboole_0(k10_relat_1(sK0,X3),k4_xboole_0(k10_relat_1(sK0,X3),X2)) = k10_relat_1(k7_relat_1(sK0,X2),X3)
    | ~ spl3_4 ),
    inference(superposition,[],[f95,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f95,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK0,X1)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f62,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f470,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f464,f454,f466])).

fof(f454,plain,
    ( spl3_8
  <=> v1_xboole_0(k4_xboole_0(k10_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f464,plain,
    ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f456,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f456,plain,
    ( v1_xboole_0(k4_xboole_0(k10_relat_1(sK0,sK2),sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f454])).

fof(f459,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f444,f50,f454])).

fof(f50,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f444,plain,
    ( v1_xboole_0(k4_xboole_0(k10_relat_1(sK0,sK2),sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f424,f67])).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X2),X2)
      | v1_xboole_0(k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f36,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f424,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k10_relat_1(sK0,sK2),X0),sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f52,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f41,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f52,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f63,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f29,f45])).

fof(f29,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:52:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (13266)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (13269)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (13278)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (13271)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (13270)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (13277)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (13268)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (13274)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (13282)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (13271)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (13279)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (13272)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (13280)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (13276)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (13276)Refutation not found, incomplete strategy% (13276)------------------------------
% 0.22/0.52  % (13276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13276)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13276)Memory used [KB]: 10618
% 0.22/0.52  % (13276)Time elapsed: 0.081 s
% 0.22/0.52  % (13276)------------------------------
% 0.22/0.52  % (13276)------------------------------
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f524,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f48,f53,f63,f459,f470,f508])).
% 0.22/0.52  fof(f508,plain,(
% 0.22/0.52    spl3_1 | ~spl3_4 | ~spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f507,f466,f60,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    spl3_1 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    spl3_4 <=> v1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f466,plain,(
% 0.22/0.52    spl3_9 <=> k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.52  fof(f507,plain,(
% 0.22/0.52    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl3_4 | ~spl3_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f493,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f30,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.52  fof(f493,plain,(
% 0.22/0.52    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) | (~spl3_4 | ~spl3_9)),
% 0.22/0.52    inference(superposition,[],[f128,f468])).
% 0.22/0.52  fof(f468,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1) | ~spl3_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f466])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k4_xboole_0(k10_relat_1(sK0,X3),k4_xboole_0(k10_relat_1(sK0,X3),X2)) = k10_relat_1(k7_relat_1(sK0,X2),X3)) ) | ~spl3_4),
% 0.22/0.52    inference(superposition,[],[f95,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f34,f35,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK0,X1)))) ) | ~spl3_4),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f62,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f40,f35])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    v1_relat_1(sK0) | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f60])).
% 0.22/0.52  fof(f470,plain,(
% 0.22/0.52    spl3_9 | ~spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f464,f454,f466])).
% 0.22/0.52  fof(f454,plain,(
% 0.22/0.52    spl3_8 <=> v1_xboole_0(k4_xboole_0(k10_relat_1(sK0,sK2),sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.52  fof(f464,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK0,sK2),sK1) | ~spl3_8),
% 0.22/0.52    inference(resolution,[],[f456,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.52  fof(f456,plain,(
% 0.22/0.52    v1_xboole_0(k4_xboole_0(k10_relat_1(sK0,sK2),sK1)) | ~spl3_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f454])).
% 0.22/0.52  fof(f459,plain,(
% 0.22/0.52    spl3_8 | ~spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f444,f50,f454])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    spl3_2 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f444,plain,(
% 0.22/0.52    v1_xboole_0(k4_xboole_0(k10_relat_1(sK0,sK2),sK1)) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f424,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~r1_tarski(k4_xboole_0(X1,X2),X2) | v1_xboole_0(k4_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(resolution,[],[f36,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.52  fof(f424,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k4_xboole_0(k10_relat_1(sK0,sK2),X0),sK1)) ) | ~spl3_2),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f52,f142])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.52    inference(superposition,[],[f41,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f33,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f50])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f60])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f28,f50])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ~spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f29,f45])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (13271)------------------------------
% 0.22/0.52  % (13271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13271)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (13271)Memory used [KB]: 6396
% 0.22/0.52  % (13271)Time elapsed: 0.075 s
% 0.22/0.52  % (13271)------------------------------
% 0.22/0.52  % (13271)------------------------------
% 0.22/0.52  % (13264)Success in time 0.158 s
%------------------------------------------------------------------------------

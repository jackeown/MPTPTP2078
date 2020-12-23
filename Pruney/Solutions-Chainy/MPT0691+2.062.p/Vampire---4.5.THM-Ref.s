%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:53 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 112 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 263 expanded)
%              Number of equality atoms :   47 (  59 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f236])).

fof(f236,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f234,f29])).

fof(f29,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f234,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f228,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f65,f44])).

fof(f44,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) ),
    inference(resolution,[],[f45,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f228,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_3 ),
    inference(superposition,[],[f108,f91])).

fof(f91,plain,
    ( sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f90,f75])).

fof(f75,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f74,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f90,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f89,f63])).

fof(f63,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f89,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f79,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_3
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f108,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k5_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X1),X2))
      | r1_tarski(X1,k10_relat_1(sK1,X2)) ) ),
    inference(superposition,[],[f46,f92])).

fof(f92,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f47,f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f42,f32])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f85,f27])).

fof(f85,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_3 ),
    inference(resolution,[],[f80,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f80,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.41/0.55  % (22458)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.56  % (22459)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.41/0.56  % (22476)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.56  % (22460)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.52/0.57  % (22475)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.52/0.57  % (22468)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.52/0.57  % (22468)Refutation not found, incomplete strategy% (22468)------------------------------
% 1.52/0.57  % (22468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (22468)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (22468)Memory used [KB]: 10618
% 1.52/0.57  % (22468)Time elapsed: 0.136 s
% 1.52/0.57  % (22468)------------------------------
% 1.52/0.57  % (22468)------------------------------
% 1.52/0.57  % (22453)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.52/0.57  % (22457)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.52/0.57  % (22467)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.52/0.57  % (22458)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f241,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f87,f236])).
% 1.52/0.57  fof(f236,plain,(
% 1.52/0.57    ~spl2_3),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f235])).
% 1.52/0.57  fof(f235,plain,(
% 1.52/0.57    $false | ~spl2_3),
% 1.52/0.57    inference(subsumption_resolution,[],[f234,f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.52/0.57    inference(cnf_transformation,[],[f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f15,plain,(
% 1.52/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.52/0.57    inference(flattening,[],[f14])).
% 1.52/0.57  fof(f14,plain,(
% 1.52/0.57    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,negated_conjecture,(
% 1.52/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.52/0.57    inference(negated_conjecture,[],[f11])).
% 1.52/0.57  fof(f11,conjecture,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.52/0.57  fof(f234,plain,(
% 1.52/0.57    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_3),
% 1.52/0.57    inference(subsumption_resolution,[],[f228,f67])).
% 1.52/0.57  fof(f67,plain,(
% 1.52/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.52/0.57    inference(forward_demodulation,[],[f65,f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f31,f32])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f13])).
% 1.52/0.57  fof(f13,plain,(
% 1.52/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.52/0.57    inference(rectify,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.52/0.57  fof(f65,plain,(
% 1.52/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) )),
% 1.52/0.57    inference(resolution,[],[f45,f48])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.52/0.57    inference(equality_resolution,[],[f38])).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.57    inference(flattening,[],[f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.57    inference(nnf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.57  fof(f45,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f41,f43])).
% 1.52/0.57  fof(f43,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f33,f32])).
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.52/0.57    inference(nnf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.52/0.57  fof(f228,plain,(
% 1.52/0.57    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_3),
% 1.52/0.57    inference(superposition,[],[f108,f91])).
% 1.52/0.57  fof(f91,plain,(
% 1.52/0.57    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~spl2_3),
% 1.52/0.57    inference(forward_demodulation,[],[f90,f75])).
% 1.52/0.57  fof(f75,plain,(
% 1.52/0.57    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.52/0.57    inference(subsumption_resolution,[],[f74,f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    v1_relat_1(sK1)),
% 1.52/0.57    inference(cnf_transformation,[],[f23])).
% 1.52/0.57  fof(f74,plain,(
% 1.52/0.57    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.52/0.57    inference(resolution,[],[f36,f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.52/0.57    inference(cnf_transformation,[],[f23])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(flattening,[],[f19])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.52/0.57  fof(f90,plain,(
% 1.52/0.57    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~spl2_3),
% 1.52/0.57    inference(forward_demodulation,[],[f89,f63])).
% 1.52/0.57  fof(f63,plain,(
% 1.52/0.57    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 1.52/0.57    inference(resolution,[],[f35,f27])).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f18])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f7])).
% 1.52/0.57  fof(f7,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.52/0.57  fof(f89,plain,(
% 1.52/0.57    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,sK0))) | ~spl2_3),
% 1.52/0.57    inference(resolution,[],[f79,f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.52/0.57  fof(f79,plain,(
% 1.52/0.57    v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_3),
% 1.52/0.57    inference(avatar_component_clause,[],[f78])).
% 1.52/0.57  fof(f78,plain,(
% 1.52/0.57    spl2_3 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.52/0.57  fof(f108,plain,(
% 1.52/0.57    ( ! [X2,X1] : (k1_xboole_0 != k5_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X1),X2)) | r1_tarski(X1,k10_relat_1(sK1,X2))) )),
% 1.52/0.57    inference(superposition,[],[f46,f92])).
% 1.52/0.57  fof(f92,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) )),
% 1.52/0.57    inference(resolution,[],[f47,f27])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 1.52/0.57    inference(definition_unfolding,[],[f42,f32])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f40,f43])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f87,plain,(
% 1.52/0.57    spl2_3),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f86])).
% 1.52/0.57  fof(f86,plain,(
% 1.52/0.57    $false | spl2_3),
% 1.52/0.57    inference(subsumption_resolution,[],[f85,f27])).
% 1.52/0.57  fof(f85,plain,(
% 1.52/0.57    ~v1_relat_1(sK1) | spl2_3),
% 1.52/0.57    inference(resolution,[],[f80,f34])).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.52/0.57  fof(f80,plain,(
% 1.52/0.57    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_3),
% 1.52/0.57    inference(avatar_component_clause,[],[f78])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (22458)------------------------------
% 1.52/0.57  % (22458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (22458)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (22458)Memory used [KB]: 10874
% 1.52/0.57  % (22458)Time elapsed: 0.144 s
% 1.52/0.57  % (22458)------------------------------
% 1.52/0.57  % (22458)------------------------------
% 1.52/0.58  % (22451)Success in time 0.209 s
%------------------------------------------------------------------------------

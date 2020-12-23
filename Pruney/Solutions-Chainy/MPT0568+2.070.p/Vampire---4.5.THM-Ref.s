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
% DateTime   : Thu Dec  3 12:50:19 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   67 (  89 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  116 ( 140 expanded)
%              Number of equality atoms :   52 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f75])).

fof(f75,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_2 ),
    inference(superposition,[],[f29,f70])).

% (17512)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f70,plain,
    ( ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f69,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f69,plain,
    ( ! [X2] : k10_relat_1(k1_xboole_0,X2) = k1_setfam_1(k6_enumset1(k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k1_xboole_0))
    | ~ spl4_2 ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_2
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f29,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f22])).

fof(f22,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f67,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f65,f32])).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f65,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1(k1_xboole_0)),k1_xboole_0)
    | spl4_1 ),
    inference(resolution,[],[f64,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f64,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | spl4_1 ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f27,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f59,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f63,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f55,f61,f57])).

fof(f55,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f39,f30])).

fof(f30,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (798752768)
% 0.13/0.36  ipcrm: permission denied for id (805404673)
% 0.13/0.37  ipcrm: permission denied for id (803995650)
% 0.13/0.37  ipcrm: permission denied for id (800489475)
% 0.13/0.37  ipcrm: permission denied for id (800555013)
% 0.13/0.37  ipcrm: permission denied for id (800620551)
% 0.13/0.37  ipcrm: permission denied for id (800686089)
% 0.13/0.38  ipcrm: permission denied for id (798851082)
% 0.13/0.38  ipcrm: permission denied for id (800718859)
% 0.13/0.38  ipcrm: permission denied for id (800751628)
% 0.13/0.38  ipcrm: permission denied for id (798916621)
% 0.13/0.38  ipcrm: permission denied for id (800784398)
% 0.13/0.38  ipcrm: permission denied for id (800817167)
% 0.13/0.38  ipcrm: permission denied for id (800849936)
% 0.13/0.39  ipcrm: permission denied for id (805568530)
% 0.13/0.39  ipcrm: permission denied for id (800948243)
% 0.13/0.39  ipcrm: permission denied for id (799014932)
% 0.13/0.39  ipcrm: permission denied for id (799047701)
% 0.13/0.39  ipcrm: permission denied for id (800981014)
% 0.13/0.39  ipcrm: permission denied for id (801013783)
% 0.13/0.39  ipcrm: permission denied for id (804192280)
% 0.13/0.39  ipcrm: permission denied for id (801079321)
% 0.13/0.40  ipcrm: permission denied for id (801112090)
% 0.13/0.40  ipcrm: permission denied for id (799113243)
% 0.13/0.40  ipcrm: permission denied for id (799146012)
% 0.13/0.40  ipcrm: permission denied for id (804225053)
% 0.13/0.40  ipcrm: permission denied for id (801177630)
% 0.13/0.40  ipcrm: permission denied for id (804257823)
% 0.13/0.40  ipcrm: permission denied for id (804290592)
% 0.13/0.40  ipcrm: permission denied for id (801275937)
% 0.13/0.41  ipcrm: permission denied for id (801308706)
% 0.13/0.41  ipcrm: permission denied for id (804323363)
% 0.13/0.41  ipcrm: permission denied for id (801374244)
% 0.13/0.41  ipcrm: permission denied for id (801407013)
% 0.13/0.41  ipcrm: permission denied for id (805601318)
% 0.13/0.41  ipcrm: permission denied for id (799277095)
% 0.13/0.41  ipcrm: permission denied for id (801472552)
% 0.13/0.41  ipcrm: permission denied for id (804388905)
% 0.13/0.42  ipcrm: permission denied for id (799375402)
% 0.13/0.42  ipcrm: permission denied for id (804421675)
% 0.13/0.42  ipcrm: permission denied for id (799440940)
% 0.21/0.42  ipcrm: permission denied for id (801570861)
% 0.21/0.42  ipcrm: permission denied for id (799473710)
% 0.21/0.42  ipcrm: permission denied for id (801603631)
% 0.21/0.42  ipcrm: permission denied for id (804454448)
% 0.21/0.42  ipcrm: permission denied for id (799539249)
% 0.21/0.43  ipcrm: permission denied for id (799572018)
% 0.21/0.43  ipcrm: permission denied for id (804519988)
% 0.21/0.43  ipcrm: permission denied for id (804552757)
% 0.21/0.43  ipcrm: permission denied for id (801767478)
% 0.21/0.43  ipcrm: permission denied for id (801833016)
% 0.21/0.43  ipcrm: permission denied for id (801865785)
% 0.21/0.44  ipcrm: permission denied for id (799637562)
% 0.21/0.44  ipcrm: permission denied for id (801898555)
% 0.21/0.44  ipcrm: permission denied for id (801931324)
% 0.21/0.44  ipcrm: permission denied for id (799670333)
% 0.21/0.44  ipcrm: permission denied for id (799703102)
% 0.21/0.44  ipcrm: permission denied for id (804618303)
% 0.21/0.44  ipcrm: permission denied for id (799735872)
% 0.21/0.44  ipcrm: permission denied for id (801996865)
% 0.21/0.45  ipcrm: permission denied for id (804651074)
% 0.21/0.45  ipcrm: permission denied for id (802062403)
% 0.21/0.45  ipcrm: permission denied for id (802127941)
% 0.21/0.45  ipcrm: permission denied for id (802160710)
% 0.21/0.45  ipcrm: permission denied for id (802193479)
% 0.21/0.45  ipcrm: permission denied for id (802226248)
% 0.21/0.45  ipcrm: permission denied for id (804716617)
% 0.21/0.46  ipcrm: permission denied for id (805797964)
% 0.21/0.46  ipcrm: permission denied for id (802422861)
% 0.21/0.46  ipcrm: permission denied for id (802455630)
% 0.21/0.46  ipcrm: permission denied for id (805830735)
% 0.21/0.46  ipcrm: permission denied for id (802553937)
% 0.21/0.47  ipcrm: permission denied for id (799866962)
% 0.21/0.47  ipcrm: permission denied for id (802586707)
% 0.21/0.47  ipcrm: permission denied for id (802619476)
% 0.21/0.47  ipcrm: permission denied for id (802652245)
% 0.21/0.47  ipcrm: permission denied for id (802685014)
% 0.21/0.47  ipcrm: permission denied for id (802717783)
% 0.21/0.47  ipcrm: permission denied for id (802750552)
% 0.21/0.47  ipcrm: permission denied for id (802783321)
% 0.21/0.48  ipcrm: permission denied for id (804913242)
% 0.21/0.48  ipcrm: permission denied for id (799965275)
% 0.21/0.48  ipcrm: permission denied for id (802848860)
% 0.21/0.48  ipcrm: permission denied for id (805896285)
% 0.21/0.48  ipcrm: permission denied for id (804978782)
% 0.21/0.48  ipcrm: permission denied for id (800030815)
% 0.21/0.48  ipcrm: permission denied for id (802947168)
% 0.21/0.49  ipcrm: permission denied for id (800096354)
% 0.21/0.49  ipcrm: permission denied for id (803012707)
% 0.21/0.49  ipcrm: permission denied for id (803078244)
% 0.21/0.49  ipcrm: permission denied for id (803111013)
% 0.21/0.49  ipcrm: permission denied for id (803143782)
% 0.21/0.49  ipcrm: permission denied for id (805044327)
% 0.21/0.49  ipcrm: permission denied for id (803242089)
% 0.21/0.50  ipcrm: permission denied for id (803274858)
% 0.21/0.50  ipcrm: permission denied for id (800227435)
% 0.21/0.50  ipcrm: permission denied for id (805994604)
% 0.21/0.50  ipcrm: permission denied for id (803340397)
% 0.21/0.50  ipcrm: permission denied for id (803405935)
% 0.21/0.50  ipcrm: permission denied for id (806092913)
% 0.21/0.51  ipcrm: permission denied for id (803537010)
% 0.21/0.51  ipcrm: permission denied for id (803569779)
% 0.21/0.51  ipcrm: permission denied for id (805240948)
% 0.21/0.51  ipcrm: permission denied for id (803635317)
% 0.21/0.51  ipcrm: permission denied for id (803700855)
% 0.21/0.51  ipcrm: permission denied for id (805306488)
% 0.21/0.51  ipcrm: permission denied for id (803766393)
% 0.21/0.52  ipcrm: permission denied for id (806158458)
% 0.21/0.52  ipcrm: permission denied for id (803831931)
% 0.21/0.52  ipcrm: permission denied for id (806191228)
% 0.21/0.52  ipcrm: permission denied for id (803897469)
% 0.21/0.52  ipcrm: permission denied for id (800391294)
% 0.21/0.52  ipcrm: permission denied for id (803930239)
% 1.06/0.67  % (17492)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.06/0.68  % (17492)Refutation not found, incomplete strategy% (17492)------------------------------
% 1.06/0.68  % (17492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.68  % (17492)Termination reason: Refutation not found, incomplete strategy
% 1.06/0.68  
% 1.06/0.68  % (17492)Memory used [KB]: 10618
% 1.06/0.68  % (17492)Time elapsed: 0.104 s
% 1.06/0.68  % (17492)------------------------------
% 1.06/0.68  % (17492)------------------------------
% 1.06/0.68  % (17493)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.06/0.68  % (17493)Refutation found. Thanks to Tanya!
% 1.06/0.68  % SZS status Theorem for theBenchmark
% 1.06/0.68  % SZS output start Proof for theBenchmark
% 1.06/0.68  fof(f78,plain,(
% 1.06/0.68    $false),
% 1.06/0.68    inference(avatar_sat_refutation,[],[f63,f67,f75])).
% 1.06/0.68  fof(f75,plain,(
% 1.06/0.68    ~spl4_2),
% 1.06/0.68    inference(avatar_contradiction_clause,[],[f74])).
% 1.06/0.68  fof(f74,plain,(
% 1.06/0.68    $false | ~spl4_2),
% 1.06/0.68    inference(trivial_inequality_removal,[],[f72])).
% 1.06/0.68  fof(f72,plain,(
% 1.06/0.68    k1_xboole_0 != k1_xboole_0 | ~spl4_2),
% 1.06/0.68    inference(superposition,[],[f29,f70])).
% 1.06/0.68  % (17512)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.06/0.68  fof(f70,plain,(
% 1.06/0.68    ( ! [X2] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)) ) | ~spl4_2),
% 1.06/0.68    inference(forward_demodulation,[],[f69,f53])).
% 1.06/0.68  fof(f53,plain,(
% 1.06/0.68    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.06/0.68    inference(definition_unfolding,[],[f33,f52])).
% 1.06/0.68  fof(f52,plain,(
% 1.06/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.06/0.68    inference(definition_unfolding,[],[f37,f51])).
% 1.06/0.68  fof(f51,plain,(
% 1.06/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.06/0.68    inference(definition_unfolding,[],[f38,f50])).
% 1.06/0.68  fof(f50,plain,(
% 1.06/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.06/0.68    inference(definition_unfolding,[],[f42,f49])).
% 1.06/0.68  fof(f49,plain,(
% 1.06/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.06/0.68    inference(definition_unfolding,[],[f43,f48])).
% 1.06/0.68  fof(f48,plain,(
% 1.06/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.06/0.68    inference(definition_unfolding,[],[f44,f47])).
% 1.06/0.68  fof(f47,plain,(
% 1.06/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.06/0.68    inference(definition_unfolding,[],[f45,f46])).
% 1.06/0.68  fof(f46,plain,(
% 1.06/0.68    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f9])).
% 1.06/0.68  fof(f9,axiom,(
% 1.06/0.68    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.06/0.68  fof(f45,plain,(
% 1.06/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f8])).
% 1.06/0.68  fof(f8,axiom,(
% 1.06/0.68    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.06/0.68  fof(f44,plain,(
% 1.06/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f7])).
% 1.06/0.68  fof(f7,axiom,(
% 1.06/0.68    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.06/0.68  fof(f43,plain,(
% 1.06/0.68    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f6])).
% 1.06/0.68  fof(f6,axiom,(
% 1.06/0.68    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.06/0.68  fof(f42,plain,(
% 1.06/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f5])).
% 1.06/0.68  fof(f5,axiom,(
% 1.06/0.68    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.06/0.68  fof(f38,plain,(
% 1.06/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f4])).
% 1.06/0.68  fof(f4,axiom,(
% 1.06/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.06/0.68  fof(f37,plain,(
% 1.06/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.06/0.68    inference(cnf_transformation,[],[f11])).
% 1.06/0.68  fof(f11,axiom,(
% 1.06/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.06/0.68  fof(f33,plain,(
% 1.06/0.68    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f2])).
% 1.06/0.68  fof(f2,axiom,(
% 1.06/0.68    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.06/0.68  fof(f69,plain,(
% 1.06/0.68    ( ! [X2] : (k10_relat_1(k1_xboole_0,X2) = k1_setfam_1(k6_enumset1(k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,X2),k1_xboole_0))) ) | ~spl4_2),
% 1.06/0.68    inference(resolution,[],[f54,f62])).
% 1.06/0.68  fof(f62,plain,(
% 1.06/0.68    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl4_2),
% 1.06/0.68    inference(avatar_component_clause,[],[f61])).
% 1.06/0.68  fof(f61,plain,(
% 1.06/0.68    spl4_2 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 1.06/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.06/0.68  fof(f54,plain,(
% 1.06/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0) )),
% 1.06/0.68    inference(definition_unfolding,[],[f40,f52])).
% 1.06/0.68  fof(f40,plain,(
% 1.06/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f20])).
% 1.06/0.68  fof(f20,plain,(
% 1.06/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.06/0.68    inference(ennf_transformation,[],[f1])).
% 1.06/0.68  fof(f1,axiom,(
% 1.06/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.06/0.68  fof(f29,plain,(
% 1.06/0.68    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.06/0.68    inference(cnf_transformation,[],[f23])).
% 1.06/0.68  fof(f23,plain,(
% 1.06/0.68    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.06/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f22])).
% 1.06/0.68  fof(f22,plain,(
% 1.06/0.68    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.06/0.68    introduced(choice_axiom,[])).
% 1.06/0.68  fof(f17,plain,(
% 1.06/0.68    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.06/0.68    inference(ennf_transformation,[],[f16])).
% 1.06/0.68  fof(f16,negated_conjecture,(
% 1.06/0.68    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.06/0.68    inference(negated_conjecture,[],[f15])).
% 1.06/0.68  fof(f15,conjecture,(
% 1.06/0.68    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 1.06/0.68  fof(f67,plain,(
% 1.06/0.68    spl4_1),
% 1.06/0.68    inference(avatar_contradiction_clause,[],[f66])).
% 1.06/0.68  fof(f66,plain,(
% 1.06/0.68    $false | spl4_1),
% 1.06/0.68    inference(subsumption_resolution,[],[f65,f32])).
% 1.06/0.68  fof(f32,plain,(
% 1.06/0.68    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f3])).
% 1.06/0.68  fof(f3,axiom,(
% 1.06/0.68    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.06/0.68  fof(f65,plain,(
% 1.06/0.68    ~r1_xboole_0(k1_tarski(sK1(k1_xboole_0)),k1_xboole_0) | spl4_1),
% 1.06/0.68    inference(resolution,[],[f64,f41])).
% 1.06/0.68  fof(f41,plain,(
% 1.06/0.68    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f21])).
% 1.06/0.68  fof(f21,plain,(
% 1.06/0.68    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.06/0.68    inference(ennf_transformation,[],[f10])).
% 1.06/0.68  fof(f10,axiom,(
% 1.06/0.68    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.06/0.68  fof(f64,plain,(
% 1.06/0.68    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | spl4_1),
% 1.06/0.68    inference(resolution,[],[f59,f35])).
% 1.06/0.68  fof(f35,plain,(
% 1.06/0.68    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f28])).
% 1.06/0.68  fof(f28,plain,(
% 1.06/0.68    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.06/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f27,f26])).
% 1.06/0.68  fof(f26,plain,(
% 1.06/0.68    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.06/0.68    introduced(choice_axiom,[])).
% 1.06/0.68  fof(f27,plain,(
% 1.06/0.68    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 1.06/0.68    introduced(choice_axiom,[])).
% 1.06/0.68  fof(f25,plain,(
% 1.06/0.68    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.06/0.68    inference(rectify,[],[f24])).
% 1.06/0.68  fof(f24,plain,(
% 1.06/0.68    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.06/0.68    inference(nnf_transformation,[],[f18])).
% 1.06/0.68  fof(f18,plain,(
% 1.06/0.68    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.06/0.68    inference(ennf_transformation,[],[f12])).
% 1.06/0.68  fof(f12,axiom,(
% 1.06/0.68    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.06/0.68  fof(f59,plain,(
% 1.06/0.68    ~v1_relat_1(k1_xboole_0) | spl4_1),
% 1.06/0.68    inference(avatar_component_clause,[],[f57])).
% 1.06/0.68  fof(f57,plain,(
% 1.06/0.68    spl4_1 <=> v1_relat_1(k1_xboole_0)),
% 1.06/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.06/0.68  fof(f63,plain,(
% 1.06/0.68    ~spl4_1 | spl4_2),
% 1.06/0.68    inference(avatar_split_clause,[],[f55,f61,f57])).
% 1.06/0.68  fof(f55,plain,(
% 1.06/0.68    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.06/0.68    inference(superposition,[],[f39,f30])).
% 1.06/0.68  fof(f30,plain,(
% 1.06/0.68    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.06/0.68    inference(cnf_transformation,[],[f14])).
% 1.06/0.68  fof(f14,axiom,(
% 1.06/0.68    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.06/0.68  fof(f39,plain,(
% 1.06/0.68    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.06/0.68    inference(cnf_transformation,[],[f19])).
% 1.06/0.68  fof(f19,plain,(
% 1.06/0.68    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.06/0.68    inference(ennf_transformation,[],[f13])).
% 1.06/0.68  fof(f13,axiom,(
% 1.06/0.68    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.06/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.06/0.68  % SZS output end Proof for theBenchmark
% 1.06/0.68  % (17493)------------------------------
% 1.06/0.68  % (17493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.68  % (17493)Termination reason: Refutation
% 1.06/0.68  
% 1.06/0.68  % (17493)Memory used [KB]: 10618
% 1.06/0.68  % (17493)Time elapsed: 0.120 s
% 1.06/0.68  % (17493)------------------------------
% 1.06/0.68  % (17493)------------------------------
% 1.06/0.69  % (17512)Refutation not found, incomplete strategy% (17512)------------------------------
% 1.06/0.69  % (17512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.69  % (17512)Termination reason: Refutation not found, incomplete strategy
% 1.06/0.69  
% 1.06/0.69  % (17512)Memory used [KB]: 10618
% 1.06/0.69  % (17512)Time elapsed: 0.007 s
% 1.06/0.69  % (17512)------------------------------
% 1.06/0.69  % (17512)------------------------------
% 1.06/0.69  % (17501)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.06/0.69  % (17496)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.06/0.69  % (17501)Refutation not found, incomplete strategy% (17501)------------------------------
% 1.06/0.69  % (17501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.69  % (17501)Termination reason: Refutation not found, incomplete strategy
% 1.06/0.69  
% 1.06/0.69  % (17501)Memory used [KB]: 10618
% 1.06/0.69  % (17501)Time elapsed: 0.133 s
% 1.06/0.69  % (17501)------------------------------
% 1.06/0.69  % (17501)------------------------------
% 1.06/0.70  % (17353)Success in time 0.337 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 179 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  140 ( 352 expanded)
%              Number of equality atoms :   64 ( 146 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f936,plain,(
    $false ),
    inference(subsumption_resolution,[],[f935,f87])).

fof(f87,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f27,f85])).

fof(f85,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(resolution,[],[f82,f28])).

fof(f28,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f82,plain,(
    ! [X5] :
      ( r2_hidden(X5,k1_relat_1(sK1))
      | k1_xboole_0 = k11_relat_1(sK1,X5) ) ),
    inference(subsumption_resolution,[],[f80,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k11_relat_1(sK1,X1))
      | r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f73,f64])).

fof(f64,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ r2_hidden(X0,k11_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f47,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f80,plain,(
    ! [X5] :
      ( r2_hidden(X5,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(sK2(k11_relat_1(sK1,X5)),sK3(k11_relat_1(sK1,X5))),k11_relat_1(sK1,X5))
      | k1_xboole_0 = k11_relat_1(sK1,X5) ) ),
    inference(resolution,[],[f77,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f77,plain,(
    ! [X2] :
      ( v1_relat_1(k11_relat_1(sK1,X2))
      | r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f74,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f27,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f935,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f934])).

fof(f934,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f933,f85])).

fof(f933,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f542,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f542,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_relat_1(sK1))
      | k1_xboole_0 != k11_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f541,f29])).

fof(f541,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f540,f200])).

fof(f200,plain,(
    ! [X0] : k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[],[f60,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f60,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f540,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f39,f506])).

fof(f506,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f59,f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f33,f58])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (5079)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.48  % (5096)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (5096)Refutation not found, incomplete strategy% (5096)------------------------------
% 0.20/0.49  % (5096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5096)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (5096)Memory used [KB]: 10746
% 0.20/0.49  % (5096)Time elapsed: 0.069 s
% 0.20/0.49  % (5096)------------------------------
% 0.20/0.49  % (5096)------------------------------
% 0.20/0.56  % (5079)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f936,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(subsumption_resolution,[],[f935,f87])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f86])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.56    inference(backward_demodulation,[],[f27,f85])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f83])).
% 0.20/0.56  fof(f83,plain,(
% 0.20/0.56    k1_xboole_0 = k11_relat_1(sK1,sK0) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.20/0.56    inference(resolution,[],[f82,f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.56    inference(negated_conjecture,[],[f17])).
% 0.20/0.56  fof(f17,conjecture,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    ( ! [X5] : (r2_hidden(X5,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X5)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f80,f74])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK1,X1)) | r2_hidden(X1,k1_relat_1(sK1))) )),
% 0.20/0.56    inference(resolution,[],[f73,f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.56    inference(equality_resolution,[],[f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK1) | ~r2_hidden(X0,k11_relat_1(sK1,X1))) )),
% 0.20/0.56    inference(resolution,[],[f47,f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    v1_relat_1(sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.56    inference(ennf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    ( ! [X5] : (r2_hidden(X5,k1_relat_1(sK1)) | r2_hidden(k4_tarski(sK2(k11_relat_1(sK1,X5)),sK3(k11_relat_1(sK1,X5))),k11_relat_1(sK1,X5)) | k1_xboole_0 = k11_relat_1(sK1,X5)) )),
% 0.20/0.56    inference(resolution,[],[f77,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    ( ! [X2] : (v1_relat_1(k11_relat_1(sK1,X2)) | r2_hidden(X2,k1_relat_1(sK1))) )),
% 0.20/0.56    inference(resolution,[],[f74,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f935,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f934])).
% 0.20/0.56  fof(f934,plain,(
% 0.20/0.56    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.56    inference(superposition,[],[f933,f85])).
% 0.20/0.56  fof(f933,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.20/0.56    inference(resolution,[],[f542,f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f44,f58])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f31,f57])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f38,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f46,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f49,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f50,f53])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f51,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.56  fof(f542,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_relat_1(sK1)) | k1_xboole_0 != k11_relat_1(sK1,X0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f541,f29])).
% 0.20/0.56  fof(f541,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f540,f200])).
% 0.20/0.56  fof(f200,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.56    inference(superposition,[],[f60,f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f37,f58])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.56  fof(f540,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.20/0.56    inference(superposition,[],[f39,f506])).
% 0.20/0.56  fof(f506,plain,(
% 0.20/0.56    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 0.20/0.56    inference(resolution,[],[f59,f29])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f33,f58])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.20/0.56    inference(flattening,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (5079)------------------------------
% 0.20/0.56  % (5079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (5079)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (5079)Memory used [KB]: 7547
% 0.20/0.56  % (5079)Time elapsed: 0.135 s
% 0.20/0.56  % (5079)------------------------------
% 0.20/0.56  % (5079)------------------------------
% 0.20/0.56  % (5093)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (5097)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (5066)Success in time 0.208 s
%------------------------------------------------------------------------------

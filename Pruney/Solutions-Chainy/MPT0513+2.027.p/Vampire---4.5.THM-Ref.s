%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:47 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   51 (  53 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 (  83 expanded)
%              Number of equality atoms :   51 (  53 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f84,f77])).

fof(f77,plain,(
    ! [X6] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f71,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f71,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f47,f58])).

fof(f58,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f44,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f84,plain,(
    ! [X0] : k7_relat_1(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f48,f76])).

fof(f76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f67,f74])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f57,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f70,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f47,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f57,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f67,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f49,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f35,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f30])).

fof(f30,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (12645)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.55  % (12637)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.56  % (12637)Refutation not found, incomplete strategy% (12637)------------------------------
% 1.40/0.56  % (12637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (12637)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (12637)Memory used [KB]: 6140
% 1.40/0.56  % (12637)Time elapsed: 0.073 s
% 1.40/0.56  % (12637)------------------------------
% 1.40/0.56  % (12637)------------------------------
% 1.40/0.56  % (12628)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.56  % (12630)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.56  % (12629)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.56  % (12630)Refutation not found, incomplete strategy% (12630)------------------------------
% 1.40/0.56  % (12630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (12630)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (12630)Memory used [KB]: 10618
% 1.40/0.56  % (12630)Time elapsed: 0.137 s
% 1.40/0.56  % (12630)------------------------------
% 1.40/0.56  % (12630)------------------------------
% 1.40/0.57  % (12629)Refutation found. Thanks to Tanya!
% 1.40/0.57  % SZS status Theorem for theBenchmark
% 1.40/0.57  % (12622)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.57  % (12622)Refutation not found, incomplete strategy% (12622)------------------------------
% 1.40/0.57  % (12622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (12622)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (12622)Memory used [KB]: 1663
% 1.40/0.57  % (12622)Time elapsed: 0.143 s
% 1.40/0.57  % (12622)------------------------------
% 1.40/0.57  % (12622)------------------------------
% 1.71/0.58  % SZS output start Proof for theBenchmark
% 1.71/0.58  fof(f86,plain,(
% 1.71/0.58    $false),
% 1.71/0.58    inference(subsumption_resolution,[],[f35,f85])).
% 1.71/0.58  fof(f85,plain,(
% 1.71/0.58    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.71/0.58    inference(forward_demodulation,[],[f84,f77])).
% 1.71/0.58  fof(f77,plain,(
% 1.71/0.58    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)) )),
% 1.71/0.58    inference(forward_demodulation,[],[f71,f36])).
% 1.71/0.58  fof(f36,plain,(
% 1.71/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f5])).
% 1.71/0.58  fof(f5,axiom,(
% 1.71/0.58    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.71/0.58  fof(f71,plain,(
% 1.71/0.58    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 1.71/0.58    inference(superposition,[],[f47,f58])).
% 1.71/0.58  fof(f58,plain,(
% 1.71/0.58    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.71/0.58    inference(superposition,[],[f44,f38])).
% 1.71/0.58  fof(f38,plain,(
% 1.71/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.71/0.58    inference(cnf_transformation,[],[f6])).
% 1.71/0.58  fof(f6,axiom,(
% 1.71/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.71/0.58  fof(f44,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f1])).
% 1.71/0.58  fof(f1,axiom,(
% 1.71/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.71/0.58  fof(f47,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f3])).
% 1.71/0.58  fof(f3,axiom,(
% 1.71/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.71/0.58  fof(f84,plain,(
% 1.71/0.58    ( ! [X0] : (k7_relat_1(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0)))) )),
% 1.71/0.58    inference(resolution,[],[f48,f76])).
% 1.71/0.58  fof(f76,plain,(
% 1.71/0.58    v1_relat_1(k1_xboole_0)),
% 1.71/0.58    inference(subsumption_resolution,[],[f67,f74])).
% 1.71/0.58  fof(f74,plain,(
% 1.71/0.58    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 1.71/0.58    inference(backward_demodulation,[],[f57,f73])).
% 1.71/0.58  fof(f73,plain,(
% 1.71/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.71/0.58    inference(forward_demodulation,[],[f70,f37])).
% 1.71/0.58  fof(f37,plain,(
% 1.71/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f7])).
% 1.71/0.58  fof(f7,axiom,(
% 1.71/0.58    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.71/0.58  fof(f70,plain,(
% 1.71/0.58    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 1.71/0.58    inference(superposition,[],[f47,f43])).
% 1.71/0.58  fof(f43,plain,(
% 1.71/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.71/0.58    inference(cnf_transformation,[],[f22])).
% 1.71/0.58  fof(f22,plain,(
% 1.71/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.71/0.58    inference(rectify,[],[f2])).
% 1.71/0.58  fof(f2,axiom,(
% 1.71/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.71/0.58  fof(f57,plain,(
% 1.71/0.58    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.71/0.58    inference(equality_resolution,[],[f50])).
% 1.71/0.58  fof(f50,plain,(
% 1.71/0.58    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f34])).
% 1.71/0.58  fof(f34,plain,(
% 1.71/0.58    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.71/0.58    inference(nnf_transformation,[],[f16])).
% 1.71/0.58  fof(f16,axiom,(
% 1.71/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.71/0.58  fof(f67,plain,(
% 1.71/0.58    v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0))),
% 1.71/0.58    inference(resolution,[],[f66,f41])).
% 1.71/0.58  fof(f41,plain,(
% 1.71/0.58    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f33])).
% 1.71/0.58  fof(f33,plain,(
% 1.71/0.58    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.71/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f32])).
% 1.71/0.58  fof(f32,plain,(
% 1.71/0.58    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f27,plain,(
% 1.71/0.58    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.71/0.58    inference(ennf_transformation,[],[f23])).
% 1.71/0.58  fof(f23,plain,(
% 1.71/0.58    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.71/0.58    inference(unused_predicate_definition_removal,[],[f18])).
% 1.71/0.58  fof(f18,axiom,(
% 1.71/0.58    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.71/0.58  fof(f66,plain,(
% 1.71/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.71/0.58    inference(resolution,[],[f49,f40])).
% 1.71/0.58  fof(f40,plain,(
% 1.71/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.71/0.58    inference(cnf_transformation,[],[f26])).
% 1.71/0.58  fof(f26,plain,(
% 1.71/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.71/0.58    inference(ennf_transformation,[],[f4])).
% 1.71/0.58  fof(f4,axiom,(
% 1.71/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.71/0.58  fof(f49,plain,(
% 1.71/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f29])).
% 1.71/0.58  fof(f29,plain,(
% 1.71/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 1.71/0.58    inference(ennf_transformation,[],[f24])).
% 1.71/0.58  fof(f24,plain,(
% 1.71/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 1.71/0.58    inference(unused_predicate_definition_removal,[],[f15])).
% 1.71/0.58  fof(f15,axiom,(
% 1.71/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.71/0.58  fof(f48,plain,(
% 1.71/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f28])).
% 1.71/0.58  fof(f28,plain,(
% 1.71/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.71/0.58    inference(ennf_transformation,[],[f19])).
% 1.71/0.58  fof(f19,axiom,(
% 1.71/0.58    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).
% 1.71/0.58  fof(f35,plain,(
% 1.71/0.58    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 1.71/0.58    inference(cnf_transformation,[],[f31])).
% 1.71/0.58  fof(f31,plain,(
% 1.71/0.58    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 1.71/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f30])).
% 1.71/0.58  fof(f30,plain,(
% 1.71/0.58    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f25,plain,(
% 1.71/0.58    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 1.71/0.58    inference(ennf_transformation,[],[f21])).
% 1.71/0.58  fof(f21,negated_conjecture,(
% 1.71/0.58    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.71/0.58    inference(negated_conjecture,[],[f20])).
% 1.71/0.58  fof(f20,conjecture,(
% 1.71/0.58    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.71/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 1.71/0.58  % SZS output end Proof for theBenchmark
% 1.71/0.58  % (12629)------------------------------
% 1.71/0.58  % (12629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (12629)Termination reason: Refutation
% 1.71/0.58  
% 1.71/0.58  % (12629)Memory used [KB]: 6268
% 1.71/0.58  % (12629)Time elapsed: 0.087 s
% 1.71/0.58  % (12629)------------------------------
% 1.71/0.58  % (12629)------------------------------
% 1.71/0.58  % (12621)Success in time 0.217 s
%------------------------------------------------------------------------------

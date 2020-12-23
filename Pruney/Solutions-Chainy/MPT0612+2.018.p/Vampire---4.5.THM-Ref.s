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
% DateTime   : Thu Dec  3 12:51:38 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   41 (  64 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 167 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f32,f59])).

fof(f59,plain,(
    k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(superposition,[],[f58,f52])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X0)) ),
    inference(resolution,[],[f50,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_xboole_0(X0,k7_relat_1(X0,X1)) = k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f33,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | k4_xboole_0(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f29,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,sK1)),sK0) ),
    inference(resolution,[],[f56,f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,k4_xboole_0(X1,sK1)),sK0) ) ),
    inference(resolution,[],[f46,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ v1_relat_1(X6)
      | ~ r1_tarski(X3,X5)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X6,k4_xboole_0(X4,X5)),X3) ) ),
    inference(resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X1,X0)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f32,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(definition_unfolding,[],[f23,f28])).

fof(f23,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:02:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.45  % (21864)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.17/0.45  % (21864)Refutation found. Thanks to Tanya!
% 0.17/0.45  % SZS status Theorem for theBenchmark
% 0.17/0.45  % SZS output start Proof for theBenchmark
% 0.17/0.45  fof(f64,plain,(
% 0.17/0.45    $false),
% 0.17/0.45    inference(trivial_inequality_removal,[],[f63])).
% 0.17/0.45  fof(f63,plain,(
% 0.17/0.45    k1_xboole_0 != k1_xboole_0),
% 0.17/0.45    inference(superposition,[],[f32,f59])).
% 0.17/0.45  fof(f59,plain,(
% 0.17/0.45    k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.17/0.45    inference(superposition,[],[f58,f52])).
% 0.17/0.45  fof(f52,plain,(
% 0.17/0.45    ( ! [X0] : (k4_xboole_0(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X0))) )),
% 0.17/0.45    inference(resolution,[],[f50,f21])).
% 0.17/0.45  fof(f21,plain,(
% 0.17/0.45    v1_relat_1(sK2)),
% 0.17/0.45    inference(cnf_transformation,[],[f18])).
% 0.17/0.45  fof(f18,plain,(
% 0.17/0.45    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).
% 0.17/0.45  fof(f17,plain,(
% 0.17/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f10,plain,(
% 0.17/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.17/0.45    inference(flattening,[],[f9])).
% 0.17/0.45  fof(f9,plain,(
% 0.17/0.45    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.17/0.45    inference(ennf_transformation,[],[f8])).
% 0.17/0.45  fof(f8,negated_conjecture,(
% 0.17/0.45    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.17/0.45    inference(negated_conjecture,[],[f7])).
% 0.17/0.45  fof(f7,conjecture,(
% 0.17/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).
% 0.17/0.45  fof(f50,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_xboole_0(X0,k7_relat_1(X0,X1)) = k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),X1))) )),
% 0.17/0.45    inference(resolution,[],[f33,f34])).
% 0.17/0.45  fof(f34,plain,(
% 0.17/0.45    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.17/0.45    inference(equality_resolution,[],[f26])).
% 0.17/0.45  fof(f26,plain,(
% 0.17/0.45    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.17/0.45    inference(cnf_transformation,[],[f20])).
% 0.17/0.45  fof(f20,plain,(
% 0.17/0.45    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.45    inference(flattening,[],[f19])).
% 0.17/0.45  fof(f19,plain,(
% 0.17/0.45    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.45    inference(nnf_transformation,[],[f2])).
% 0.17/0.45  fof(f2,axiom,(
% 0.17/0.45    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.45  fof(f33,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | k4_xboole_0(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.17/0.45    inference(definition_unfolding,[],[f29,f28,f28])).
% 0.17/0.45  fof(f28,plain,(
% 0.17/0.45    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f4])).
% 0.17/0.45  fof(f4,axiom,(
% 0.17/0.45    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.17/0.45  fof(f29,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f14])).
% 0.17/0.45  fof(f14,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.17/0.45    inference(flattening,[],[f13])).
% 0.17/0.45  fof(f13,plain,(
% 0.17/0.45    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 0.17/0.45    inference(ennf_transformation,[],[f6])).
% 0.17/0.45  fof(f6,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).
% 0.17/0.45  fof(f58,plain,(
% 0.17/0.45    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,sK1)),sK0)) )),
% 0.17/0.45    inference(resolution,[],[f56,f21])).
% 0.17/0.45  fof(f56,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,k4_xboole_0(X1,sK1)),sK0)) )),
% 0.17/0.45    inference(resolution,[],[f46,f22])).
% 0.17/0.45  fof(f22,plain,(
% 0.17/0.45    r1_tarski(sK0,sK1)),
% 0.17/0.45    inference(cnf_transformation,[],[f18])).
% 0.17/0.45  fof(f46,plain,(
% 0.17/0.45    ( ! [X6,X4,X5,X3] : (~v1_relat_1(X6) | ~r1_tarski(X3,X5) | k1_xboole_0 = k7_relat_1(k7_relat_1(X6,k4_xboole_0(X4,X5)),X3)) )),
% 0.17/0.45    inference(resolution,[],[f41,f30])).
% 0.17/0.45  fof(f30,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f15])).
% 0.17/0.45  fof(f15,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.17/0.45    inference(ennf_transformation,[],[f3])).
% 0.17/0.45  fof(f3,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.17/0.45  fof(f41,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X1,X0) | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0) )),
% 0.17/0.45    inference(resolution,[],[f24,f31])).
% 0.17/0.45  fof(f31,plain,(
% 0.17/0.45    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f16])).
% 0.17/0.45  fof(f16,plain,(
% 0.17/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.17/0.45    inference(ennf_transformation,[],[f1])).
% 0.17/0.45  fof(f1,axiom,(
% 0.17/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.17/0.45  fof(f24,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0) )),
% 0.17/0.45    inference(cnf_transformation,[],[f12])).
% 0.17/0.45  fof(f12,plain,(
% 0.17/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.17/0.45    inference(flattening,[],[f11])).
% 0.17/0.45  fof(f11,plain,(
% 0.17/0.45    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.17/0.45    inference(ennf_transformation,[],[f5])).
% 0.17/0.45  fof(f5,axiom,(
% 0.17/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.17/0.45  fof(f32,plain,(
% 0.17/0.45    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.17/0.45    inference(definition_unfolding,[],[f23,f28])).
% 0.17/0.45  fof(f23,plain,(
% 0.17/0.45    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.17/0.45    inference(cnf_transformation,[],[f18])).
% 0.17/0.45  % SZS output end Proof for theBenchmark
% 0.17/0.45  % (21864)------------------------------
% 0.17/0.45  % (21864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.45  % (21864)Termination reason: Refutation
% 0.17/0.45  
% 0.17/0.45  % (21864)Memory used [KB]: 1663
% 0.17/0.45  % (21864)Time elapsed: 0.086 s
% 0.17/0.45  % (21864)------------------------------
% 0.17/0.45  % (21864)------------------------------
% 0.17/0.45  % (21858)Success in time 0.121 s
%------------------------------------------------------------------------------

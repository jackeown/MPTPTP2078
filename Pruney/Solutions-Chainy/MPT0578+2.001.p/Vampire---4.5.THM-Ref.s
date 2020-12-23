%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  75 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 ( 205 expanded)
%              Number of equality atoms :   38 (  68 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(subsumption_resolution,[],[f106,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f106,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f105,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f105,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f20,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f79,f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f79,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(X2,k10_relat_1(X3,k2_relat_1(X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(X2,k10_relat_1(X3,k2_relat_1(X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f66,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f66,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(k5_relat_1(X2,X3),k2_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(k5_relat_1(X2,X3),k2_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f57,f43])).

fof(f43,plain,(
    ! [X4,X3] :
      ( k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f37,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f37,plain,(
    ! [X4,X3] :
      ( k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f25,f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X0),k2_relat_1(X0)) = k10_relat_1(X1,k10_relat_1(X0,k2_relat_1(k5_relat_1(X1,X0))))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X0),k2_relat_1(X0)) = k10_relat_1(X1,k10_relat_1(X0,k2_relat_1(k5_relat_1(X1,X0))))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f44,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,X1) = k10_relat_1(X0,k3_xboole_0(X1,k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f24,f31])).

fof(f31,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f27,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

% (16626)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f44,plain,(
    ! [X6,X7,X5] :
      ( k10_relat_1(k5_relat_1(X5,X6),X7) = k10_relat_1(X5,k10_relat_1(X6,k3_xboole_0(k2_relat_1(k5_relat_1(X5,X6)),X7)))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f38,f26])).

fof(f38,plain,(
    ! [X6,X7,X5] :
      ( k10_relat_1(k5_relat_1(X5,X6),X7) = k10_relat_1(X5,k10_relat_1(X6,k3_xboole_0(k2_relat_1(k5_relat_1(X5,X6)),X7)))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(k5_relat_1(X5,X6)) ) ),
    inference(superposition,[],[f25,f24])).

fof(f20,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (16629)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (16629)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f106,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    v1_relat_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    ~v1_relat_1(sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f105,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    v1_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f104])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    k10_relat_1(sK0,k1_relat_1(sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.22/0.47    inference(superposition,[],[f20,f90])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f86])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(superposition,[],[f79,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(X2,k10_relat_1(X3,k2_relat_1(X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f76])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(X2,k10_relat_1(X3,k2_relat_1(X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(superposition,[],[f66,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(k5_relat_1(X2,X3),k2_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(k5_relat_1(X2,X3),k2_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(superposition,[],[f57,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4)))) | ~v1_relat_1(X4) | ~v1_relat_1(X3)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f37,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4)))) | ~v1_relat_1(X4) | ~v1_relat_1(X3) | ~v1_relat_1(k5_relat_1(X3,X4))) )),
% 0.22/0.47    inference(superposition,[],[f25,f21])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(X1,X0),k2_relat_1(X0)) = k10_relat_1(X1,k10_relat_1(X0,k2_relat_1(k5_relat_1(X1,X0)))) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(X1,X0),k2_relat_1(X0)) = k10_relat_1(X1,k10_relat_1(X0,k2_relat_1(k5_relat_1(X1,X0)))) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(superposition,[],[f44,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(X0,X1) = k10_relat_1(X0,k3_xboole_0(X1,k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(superposition,[],[f24,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.22/0.47    inference(superposition,[],[f27,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  % (16626)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.22/0.47    inference(superposition,[],[f23,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X6,X7,X5] : (k10_relat_1(k5_relat_1(X5,X6),X7) = k10_relat_1(X5,k10_relat_1(X6,k3_xboole_0(k2_relat_1(k5_relat_1(X5,X6)),X7))) | ~v1_relat_1(X6) | ~v1_relat_1(X5)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f38,f26])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X6,X7,X5] : (k10_relat_1(k5_relat_1(X5,X6),X7) = k10_relat_1(X5,k10_relat_1(X6,k3_xboole_0(k2_relat_1(k5_relat_1(X5,X6)),X7))) | ~v1_relat_1(X6) | ~v1_relat_1(X5) | ~v1_relat_1(k5_relat_1(X5,X6))) )),
% 0.22/0.47    inference(superposition,[],[f25,f24])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (16629)------------------------------
% 0.22/0.47  % (16629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (16629)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (16629)Memory used [KB]: 1663
% 0.22/0.47  % (16629)Time elapsed: 0.013 s
% 0.22/0.47  % (16629)------------------------------
% 0.22/0.47  % (16629)------------------------------
% 0.22/0.47  % (16620)Success in time 0.108 s
%------------------------------------------------------------------------------

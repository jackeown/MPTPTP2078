%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  58 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 138 expanded)
%              Number of equality atoms :   38 (  50 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f697,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f19,f20,f662])).

fof(f662,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X1,k7_relat_1(X2,X0)) = k7_relat_1(k8_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f653])).

fof(f653,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X1,k7_relat_1(X2,X0)) = k7_relat_1(k8_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f41,f517])).

fof(f517,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X2,X0),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f506])).

fof(f506,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X2,X0),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f184,f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f61,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f61,plain,(
    ! [X4,X5,X3] :
      ( k5_relat_1(k6_relat_1(X3),k5_relat_1(X4,X5)) = k5_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f58,f21])).

fof(f58,plain,(
    ! [X4,X5,X3] :
      ( k5_relat_1(k6_relat_1(X3),k5_relat_1(X4,X5)) = k5_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X4,X5,X3] :
      ( k5_relat_1(k6_relat_1(X3),k5_relat_1(X4,X5)) = k5_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f26,f23])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f41,plain,(
    ! [X4,X5,X3] :
      ( k5_relat_1(k6_relat_1(X3),k8_relat_1(X5,X4)) = k8_relat_1(X5,k7_relat_1(X4,X3))
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f37,f21])).

fof(f37,plain,(
    ! [X4,X5,X3] :
      ( k5_relat_1(k6_relat_1(X3),k8_relat_1(X5,X4)) = k8_relat_1(X5,k7_relat_1(X4,X3))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X4,X5,X3] :
      ( k5_relat_1(k6_relat_1(X3),k8_relat_1(X5,X4)) = k8_relat_1(X5,k7_relat_1(X4,X3))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f25,f24])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f20,plain,(
    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (13141)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.47  % (13157)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (13157)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f697,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f19,f20,f662])).
% 0.21/0.50  fof(f662,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X1,k7_relat_1(X2,X0)) = k7_relat_1(k8_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f653])).
% 0.21/0.50  fof(f653,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X1,k7_relat_1(X2,X0)) = k7_relat_1(k8_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(superposition,[],[f41,f517])).
% 0.21/0.50  fof(f517,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X2,X0),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f506])).
% 0.21/0.50  fof(f506,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X2,X0),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(superposition,[],[f46,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f159])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(superposition,[],[f61,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k5_relat_1(k6_relat_1(X3),k5_relat_1(X4,X5)) = k5_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X5) | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f58,f21])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k5_relat_1(k6_relat_1(X3),k5_relat_1(X4,X5)) = k5_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k5_relat_1(k6_relat_1(X3),k5_relat_1(X4,X5)) = k5_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(superposition,[],[f22,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f45,f21])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(superposition,[],[f26,f23])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k5_relat_1(k6_relat_1(X3),k8_relat_1(X5,X4)) = k8_relat_1(X5,k7_relat_1(X4,X3)) | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f37,f21])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k5_relat_1(k6_relat_1(X3),k8_relat_1(X5,X4)) = k8_relat_1(X5,k7_relat_1(X4,X3)) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k5_relat_1(k6_relat_1(X3),k8_relat_1(X5,X4)) = k8_relat_1(X5,k7_relat_1(X4,X3)) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X4)) )),
% 0.21/0.50    inference(superposition,[],[f25,f24])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2)) => (k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (13157)------------------------------
% 0.21/0.50  % (13157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13157)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (13157)Memory used [KB]: 2302
% 0.21/0.50  % (13157)Time elapsed: 0.082 s
% 0.21/0.50  % (13157)------------------------------
% 0.21/0.50  % (13157)------------------------------
% 0.21/0.50  % (13127)Success in time 0.148 s
%------------------------------------------------------------------------------

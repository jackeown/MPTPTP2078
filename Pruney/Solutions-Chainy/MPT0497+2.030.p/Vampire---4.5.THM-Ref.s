%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 169 expanded)
%              Number of leaves         :    7 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  107 ( 566 expanded)
%              Number of equality atoms :   60 ( 258 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(global_subsumption,[],[f51,f52])).

fof(f52,plain,(
    k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f50,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f20,f39])).

fof(f39,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f34,f28])).

fof(f28,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f26,f19])).

fof(f19,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),X0)
      | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    inference(global_subsumption,[],[f18,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(sK1,X0)
      | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK1,X0))
      | k1_xboole_0 = k7_relat_1(sK1,X0)
      | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f22,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(resolution,[],[f25,f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(forward_demodulation,[],[f48,f42])).

fof(f42,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f40,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f40,plain,(
    k3_xboole_0(k1_relat_1(sK1),k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f30,f37])).

fof(f37,plain,(
    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    inference(superposition,[],[f34,f21])).

fof(f48,plain,(
    k3_xboole_0(k1_relat_1(sK1),sK0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f30,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:24:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (11136)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.41  % (11136)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(global_subsumption,[],[f51,f52])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.41    inference(resolution,[],[f50,f27])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.41    inference(nnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f47])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.41    inference(superposition,[],[f20,f39])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f38])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.41    inference(duplicate_literal_removal,[],[f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.41    inference(superposition,[],[f34,f28])).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.41    inference(resolution,[],[f26,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.41    inference(flattening,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.20/0.41    inference(nnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.41    inference(negated_conjecture,[],[f6])).
% 0.20/0.41  fof(f6,conjecture,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) )),
% 0.20/0.41    inference(global_subsumption,[],[f18,f33])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,X0) | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.20/0.41    inference(resolution,[],[f32,f24])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK1,X0)) | k1_xboole_0 = k7_relat_1(sK1,X0) | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.20/0.41    inference(superposition,[],[f22,f30])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.20/0.41    inference(resolution,[],[f25,f18])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(flattening,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    v1_relat_1(sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.41    inference(forward_demodulation,[],[f48,f42])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(forward_demodulation,[],[f40,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    k3_xboole_0(k1_relat_1(sK1),k1_xboole_0) = k1_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(superposition,[],[f30,f37])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f36])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 0.20/0.41    inference(superposition,[],[f34,f21])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    k3_xboole_0(k1_relat_1(sK1),sK0) = k1_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(superposition,[],[f30,f39])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (11136)------------------------------
% 0.20/0.41  % (11136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (11136)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (11136)Memory used [KB]: 6140
% 0.20/0.41  % (11136)Time elapsed: 0.005 s
% 0.20/0.41  % (11136)------------------------------
% 0.20/0.41  % (11136)------------------------------
% 0.20/0.41  % (11125)Success in time 0.063 s
%------------------------------------------------------------------------------

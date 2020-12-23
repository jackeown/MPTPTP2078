%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 147 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   21
%              Number of atoms          :  167 ( 421 expanded)
%              Number of equality atoms :   61 ( 170 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(subsumption_resolution,[],[f300,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f300,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f297,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f297,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f36,f288])).

fof(f288,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k7_relat_1(X3,X5),X4) = k3_xboole_0(k10_relat_1(X3,X4),X5)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k7_relat_1(X3,X5),X4) = k3_xboole_0(k10_relat_1(X3,X4),X5)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f179,f155])).

fof(f155,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k5_relat_1(X2,sK3(X3))) = k10_relat_1(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f154,f42])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_relat_1(sK4(X0)) = X0
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_relat_1(X1) = X0
          & v1_relat_1(X1) )
     => ( k1_relat_1(sK4(X0)) = X0
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_xboole_0 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(f154,plain,(
    ! [X2,X3] :
      ( k10_relat_1(X2,k1_relat_1(sK4(X3))) = k1_relat_1(k5_relat_1(X2,sK3(X3)))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f153,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f153,plain,(
    ! [X2,X3] :
      ( k10_relat_1(X2,k1_relat_1(sK4(X3))) = k1_relat_1(k5_relat_1(X2,sK3(X3)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK4(X3)) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X2,X3] :
      ( k10_relat_1(X2,k1_relat_1(sK4(X3))) = k1_relat_1(k5_relat_1(X2,sK3(X3)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK4(X3))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f122,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f122,plain,(
    ! [X15,X16] :
      ( k1_relat_1(k5_relat_1(X16,sK4(X15))) = k1_relat_1(k5_relat_1(X16,sK3(X15)))
      | ~ v1_relat_1(X16) ) ),
    inference(subsumption_resolution,[],[f109,f41])).

fof(f109,plain,(
    ! [X15,X16] :
      ( k1_relat_1(k5_relat_1(X16,sK4(X15))) = k1_relat_1(k5_relat_1(X16,sK3(X15)))
      | ~ v1_relat_1(X16)
      | ~ v1_relat_1(sK4(X15)) ) ),
    inference(superposition,[],[f99,f42])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK3(k1_relat_1(X1))))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X10,X8,X9] :
      ( k1_relat_1(X9) != X8
      | k1_relat_1(k5_relat_1(X10,X9)) = k1_relat_1(k5_relat_1(X10,sK3(X8)))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f62,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_relat_1(sK3(X0)) = X0
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_relat_1(X1) = X0
          & v1_relat_1(X1) )
     => ( k1_relat_1(sK3(X0)) = X0
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_xboole_0 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f62,plain,(
    ! [X10,X8,X9] :
      ( k1_relat_1(X9) != X8
      | k1_relat_1(k5_relat_1(X10,X9)) = k1_relat_1(k5_relat_1(X10,sK3(X8)))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(sK3(X8))
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f38,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X1) != k1_relat_1(X0)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X1) != k1_relat_1(X0)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X1) = k1_relat_1(X0)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f179,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(X6,sK3(X8))),X7) = k10_relat_1(k7_relat_1(X6,X7),X8)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f178,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f178,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(X6,sK3(X8))),X7) = k10_relat_1(k7_relat_1(X6,X7),X8)
      | ~ v1_relat_1(k7_relat_1(X6,X7))
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f164,f39])).

fof(f164,plain,(
    ! [X6,X8,X7] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(X6,sK3(X8))),X7) = k10_relat_1(k7_relat_1(X6,X7),X8)
      | ~ v1_relat_1(k7_relat_1(X6,X7))
      | ~ v1_relat_1(sK3(X8))
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f155,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(X0,X1)),X2) = k1_relat_1(k5_relat_1(k7_relat_1(X0,X2),X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f56,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(X0,X1)),X2) = k1_relat_1(k5_relat_1(k7_relat_1(X0,X2),X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

% (2720)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f36,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.45  % (2729)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.46  % (2721)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.46  % (2738)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.48  % (2738)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f301,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f300,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2)) => (k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.22/0.48  fof(f300,plain,(
% 0.22/0.48    ~v1_relat_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f297,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f297,plain,(
% 0.22/0.48    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0) | ~v1_relat_1(sK2)),
% 0.22/0.48    inference(superposition,[],[f36,f288])).
% 0.22/0.48  fof(f288,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k10_relat_1(k7_relat_1(X3,X5),X4) = k3_xboole_0(k10_relat_1(X3,X4),X5) | ~v1_relat_1(X3)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f277])).
% 0.22/0.48  fof(f277,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k10_relat_1(k7_relat_1(X3,X5),X4) = k3_xboole_0(k10_relat_1(X3,X4),X5) | ~v1_relat_1(X3) | ~v1_relat_1(X3)) )),
% 0.22/0.48    inference(superposition,[],[f179,f155])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k1_relat_1(k5_relat_1(X2,sK3(X3))) = k10_relat_1(X2,X3) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f154,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0] : (k1_relat_1(sK4(X0)) = X0 & v1_relat_1(sK4(X0)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : (k1_relat_1(X1) = X0 & v1_relat_1(X1)) => (k1_relat_1(sK4(X0)) = X0 & v1_relat_1(sK4(X0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_relat_1(X1))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_xboole_0) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k10_relat_1(X2,k1_relat_1(sK4(X3))) = k1_relat_1(k5_relat_1(X2,sK3(X3))) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f153,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k10_relat_1(X2,k1_relat_1(sK4(X3))) = k1_relat_1(k5_relat_1(X2,sK3(X3))) | ~v1_relat_1(X2) | ~v1_relat_1(sK4(X3))) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f143])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k10_relat_1(X2,k1_relat_1(sK4(X3))) = k1_relat_1(k5_relat_1(X2,sK3(X3))) | ~v1_relat_1(X2) | ~v1_relat_1(sK4(X3)) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(superposition,[],[f122,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ( ! [X15,X16] : (k1_relat_1(k5_relat_1(X16,sK4(X15))) = k1_relat_1(k5_relat_1(X16,sK3(X15))) | ~v1_relat_1(X16)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f109,f41])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ( ! [X15,X16] : (k1_relat_1(k5_relat_1(X16,sK4(X15))) = k1_relat_1(k5_relat_1(X16,sK3(X15))) | ~v1_relat_1(X16) | ~v1_relat_1(sK4(X15))) )),
% 0.22/0.48    inference(superposition,[],[f99,f42])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(X0,sK3(k1_relat_1(X1)))) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X10,X8,X9] : (k1_relat_1(X9) != X8 | k1_relat_1(k5_relat_1(X10,X9)) = k1_relat_1(k5_relat_1(X10,sK3(X8))) | ~v1_relat_1(X10) | ~v1_relat_1(X9)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f62,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0] : (k1_relat_1(sK3(X0)) = X0 & v1_relat_1(sK3(X0)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : (k1_relat_1(X1) = X0 & v1_relat_1(X1)) => (k1_relat_1(sK3(X0)) = X0 & v1_relat_1(sK3(X0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_relat_1(X1))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_xboole_0) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X10,X8,X9] : (k1_relat_1(X9) != X8 | k1_relat_1(k5_relat_1(X10,X9)) = k1_relat_1(k5_relat_1(X10,sK3(X8))) | ~v1_relat_1(X10) | ~v1_relat_1(sK3(X8)) | ~v1_relat_1(X9)) )),
% 0.22/0.48    inference(superposition,[],[f38,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X1) != k1_relat_1(X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X1) = k1_relat_1(X0) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    ( ! [X6,X8,X7] : (k3_xboole_0(k1_relat_1(k5_relat_1(X6,sK3(X8))),X7) = k10_relat_1(k7_relat_1(X6,X7),X8) | ~v1_relat_1(X6)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f178,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    ( ! [X6,X8,X7] : (k3_xboole_0(k1_relat_1(k5_relat_1(X6,sK3(X8))),X7) = k10_relat_1(k7_relat_1(X6,X7),X8) | ~v1_relat_1(k7_relat_1(X6,X7)) | ~v1_relat_1(X6)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f164,f39])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    ( ! [X6,X8,X7] : (k3_xboole_0(k1_relat_1(k5_relat_1(X6,sK3(X8))),X7) = k10_relat_1(k7_relat_1(X6,X7),X8) | ~v1_relat_1(k7_relat_1(X6,X7)) | ~v1_relat_1(sK3(X8)) | ~v1_relat_1(X6)) )),
% 0.22/0.48    inference(superposition,[],[f155,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(k1_relat_1(k5_relat_1(X0,X1)),X2) = k1_relat_1(k5_relat_1(k7_relat_1(X0,X2),X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f56,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(k1_relat_1(k5_relat_1(X0,X1)),X2) = k1_relat_1(k5_relat_1(k7_relat_1(X0,X2),X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(superposition,[],[f46,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.49  % (2720)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (2738)------------------------------
% 0.22/0.49  % (2738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (2738)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (2738)Memory used [KB]: 1918
% 0.22/0.49  % (2738)Time elapsed: 0.096 s
% 0.22/0.49  % (2738)------------------------------
% 0.22/0.49  % (2738)------------------------------
% 0.22/0.50  % (2708)Success in time 0.137 s
%------------------------------------------------------------------------------

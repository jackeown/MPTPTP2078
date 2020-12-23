%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:48 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 121 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   18
%              Number of atoms          :  171 ( 341 expanded)
%              Number of equality atoms :   34 (  80 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1439,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1438,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
    ( ? [X1] :
        ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f1438,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1437,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f1437,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f1379])).

fof(f1379,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f28,f1377])).

fof(f1377,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f1373,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f57,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f57,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k10_relat_1(X3,k10_relat_1(X4,X5)),k1_relat_1(k5_relat_1(X3,X4)))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f53,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f53,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k10_relat_1(X3,k10_relat_1(X4,X5)),k1_relat_1(k5_relat_1(X3,X4)))
      | ~ v1_relat_1(k5_relat_1(X3,X4))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f1373,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0))
      | ~ r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0))) ) ),
    inference(resolution,[],[f1371,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1371,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X2,X3)),k10_relat_1(X2,k1_relat_1(X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f1370,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1370,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X2,X3)),k10_relat_1(X2,k1_relat_1(X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f1365,f35])).

fof(f1365,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X2,X3)),k10_relat_1(X2,k1_relat_1(X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ r1_tarski(k2_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3)) ) ),
    inference(superposition,[],[f1348,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(superposition,[],[f84,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_xboole_0(k2_relat_1(X0),X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_xboole_0(k2_relat_1(X0),X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f77,f47])).

fof(f47,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k10_relat_1(X3,X4))
      | k1_relat_1(X3) = k10_relat_1(X3,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f38,f32])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k10_relat_1(X0,k2_xboole_0(k2_relat_1(X0),X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k10_relat_1(X0,k2_xboole_0(k2_relat_1(X0),X1)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f66,f29])).

fof(f66,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k10_relat_1(X6,X7),k10_relat_1(X6,k2_xboole_0(X7,X8)))
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f31,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1348,plain,(
    ! [X5,X3] :
      ( r1_tarski(k10_relat_1(k5_relat_1(X5,X3),k2_relat_1(X3)),k10_relat_1(X5,k1_relat_1(X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f1333])).

fof(f1333,plain,(
    ! [X5,X3] :
      ( r1_tarski(k10_relat_1(k5_relat_1(X5,X3),k2_relat_1(X3)),k10_relat_1(X5,k1_relat_1(X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f79,f84])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k10_relat_1(k5_relat_1(X0,X1),X2),k10_relat_1(X0,k10_relat_1(X1,k2_xboole_0(X2,X3))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k10_relat_1(k5_relat_1(X0,X1),X2),k10_relat_1(X0,k10_relat_1(X1,k2_xboole_0(X2,X3))))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f66,f33])).

fof(f28,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (18043)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (18058)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.49  % (18046)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (18048)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (18047)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (18057)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (18064)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (18066)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (18061)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (18065)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (18045)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (18054)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (18056)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (18052)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (18063)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (18049)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (18044)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (18053)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (18050)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (18055)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (18062)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (18068)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (18060)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (18059)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.55  % (18067)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (18051)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.64/0.58  % (18047)Refutation found. Thanks to Tanya!
% 1.64/0.58  % SZS status Theorem for theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f1439,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(subsumption_resolution,[],[f1438,f27])).
% 1.64/0.58  fof(f27,plain,(
% 1.64/0.58    v1_relat_1(sK1)),
% 1.64/0.58    inference(cnf_transformation,[],[f23])).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).
% 1.64/0.58  fof(f21,plain,(
% 1.64/0.58    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f22,plain,(
% 1.64/0.58    ? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f12,plain,(
% 1.64/0.58    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f11])).
% 1.64/0.58  fof(f11,negated_conjecture,(
% 1.64/0.58    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.64/0.58    inference(negated_conjecture,[],[f10])).
% 1.64/0.58  fof(f10,conjecture,(
% 1.64/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.64/0.58  fof(f1438,plain,(
% 1.64/0.58    ~v1_relat_1(sK1)),
% 1.64/0.58    inference(subsumption_resolution,[],[f1437,f26])).
% 1.64/0.58  fof(f26,plain,(
% 1.64/0.58    v1_relat_1(sK0)),
% 1.64/0.58    inference(cnf_transformation,[],[f23])).
% 1.64/0.58  fof(f1437,plain,(
% 1.64/0.58    ~v1_relat_1(sK0) | ~v1_relat_1(sK1)),
% 1.64/0.58    inference(trivial_inequality_removal,[],[f1379])).
% 1.64/0.58  fof(f1379,plain,(
% 1.64/0.58    k10_relat_1(sK0,k1_relat_1(sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1)),
% 1.64/0.58    inference(superposition,[],[f28,f1377])).
% 1.64/0.58  fof(f1377,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f1373,f134])).
% 1.64/0.58  fof(f134,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 1.64/0.58    inference(duplicate_literal_removal,[],[f129])).
% 1.64/0.58  fof(f129,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(superposition,[],[f57,f29])).
% 1.64/0.58  fof(f29,plain,(
% 1.64/0.58    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f13])).
% 1.64/0.58  fof(f13,plain,(
% 1.64/0.58    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f6])).
% 1.64/0.58  fof(f6,axiom,(
% 1.64/0.58    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.64/0.58  fof(f57,plain,(
% 1.64/0.58    ( ! [X4,X5,X3] : (r1_tarski(k10_relat_1(X3,k10_relat_1(X4,X5)),k1_relat_1(k5_relat_1(X3,X4))) | ~v1_relat_1(X4) | ~v1_relat_1(X3)) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f53,f35])).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f19])).
% 1.64/0.58  fof(f19,plain,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.64/0.58    inference(flattening,[],[f18])).
% 1.64/0.58  fof(f18,plain,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.64/0.58    inference(ennf_transformation,[],[f4])).
% 1.64/0.58  fof(f4,axiom,(
% 1.64/0.58    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.64/0.58  fof(f53,plain,(
% 1.64/0.58    ( ! [X4,X5,X3] : (r1_tarski(k10_relat_1(X3,k10_relat_1(X4,X5)),k1_relat_1(k5_relat_1(X3,X4))) | ~v1_relat_1(k5_relat_1(X3,X4)) | ~v1_relat_1(X4) | ~v1_relat_1(X3)) )),
% 1.64/0.58    inference(superposition,[],[f32,f33])).
% 1.64/0.58  fof(f33,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f16])).
% 1.64/0.58  fof(f16,plain,(
% 1.64/0.58    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 1.64/0.58  fof(f32,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f15])).
% 1.64/0.58  fof(f15,plain,(
% 1.64/0.58    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f5])).
% 1.64/0.58  fof(f5,axiom,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.64/0.58  fof(f1373,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) | ~r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0)))) )),
% 1.64/0.58    inference(resolution,[],[f1371,f38])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f25])).
% 1.64/0.58  fof(f25,plain,(
% 1.64/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.58    inference(flattening,[],[f24])).
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.58    inference(nnf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.64/0.58  fof(f1371,plain,(
% 1.64/0.58    ( ! [X2,X3] : (r1_tarski(k1_relat_1(k5_relat_1(X2,X3)),k10_relat_1(X2,k1_relat_1(X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f1370,f30])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f14])).
% 1.64/0.58  fof(f14,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f9])).
% 1.64/0.58  fof(f9,axiom,(
% 1.64/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.64/0.58  fof(f1370,plain,(
% 1.64/0.58    ( ! [X2,X3] : (r1_tarski(k1_relat_1(k5_relat_1(X2,X3)),k10_relat_1(X2,k1_relat_1(X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3))) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f1365,f35])).
% 1.64/0.58  fof(f1365,plain,(
% 1.64/0.58    ( ! [X2,X3] : (r1_tarski(k1_relat_1(k5_relat_1(X2,X3)),k10_relat_1(X2,k1_relat_1(X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(k5_relat_1(X2,X3)) | ~r1_tarski(k2_relat_1(k5_relat_1(X2,X3)),k2_relat_1(X3))) )),
% 1.64/0.58    inference(superposition,[],[f1348,f87])).
% 1.64/0.58  fof(f87,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 1.64/0.58    inference(superposition,[],[f84,f34])).
% 1.64/0.58  fof(f34,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f17])).
% 1.64/0.58  fof(f17,plain,(
% 1.64/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f2])).
% 1.64/0.58  fof(f2,axiom,(
% 1.64/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.64/0.58  fof(f84,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k2_xboole_0(k2_relat_1(X0),X1)) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(duplicate_literal_removal,[],[f80])).
% 1.64/0.58  fof(f80,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_xboole_0(k2_relat_1(X0),X1)) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(resolution,[],[f77,f47])).
% 1.64/0.58  fof(f47,plain,(
% 1.64/0.58    ( ! [X4,X3] : (~r1_tarski(k1_relat_1(X3),k10_relat_1(X3,X4)) | k1_relat_1(X3) = k10_relat_1(X3,X4) | ~v1_relat_1(X3)) )),
% 1.64/0.58    inference(resolution,[],[f38,f32])).
% 1.64/0.58  fof(f77,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k10_relat_1(X0,k2_xboole_0(k2_relat_1(X0),X1))) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(duplicate_literal_removal,[],[f72])).
% 1.64/0.58  fof(f72,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k10_relat_1(X0,k2_xboole_0(k2_relat_1(X0),X1))) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(superposition,[],[f66,f29])).
% 1.64/0.58  fof(f66,plain,(
% 1.64/0.58    ( ! [X6,X8,X7] : (r1_tarski(k10_relat_1(X6,X7),k10_relat_1(X6,k2_xboole_0(X7,X8))) | ~v1_relat_1(X6)) )),
% 1.64/0.58    inference(superposition,[],[f31,f39])).
% 1.64/0.58  fof(f39,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f20])).
% 1.64/0.58  fof(f20,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.64/0.58    inference(ennf_transformation,[],[f7])).
% 1.64/0.58  fof(f7,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 1.64/0.58  fof(f31,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f3])).
% 1.64/0.58  fof(f3,axiom,(
% 1.64/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.64/0.58  fof(f1348,plain,(
% 1.64/0.58    ( ! [X5,X3] : (r1_tarski(k10_relat_1(k5_relat_1(X5,X3),k2_relat_1(X3)),k10_relat_1(X5,k1_relat_1(X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X5)) )),
% 1.64/0.58    inference(duplicate_literal_removal,[],[f1333])).
% 1.64/0.58  fof(f1333,plain,(
% 1.64/0.58    ( ! [X5,X3] : (r1_tarski(k10_relat_1(k5_relat_1(X5,X3),k2_relat_1(X3)),k10_relat_1(X5,k1_relat_1(X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X5) | ~v1_relat_1(X3)) )),
% 1.64/0.58    inference(superposition,[],[f79,f84])).
% 1.64/0.58  fof(f79,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k10_relat_1(k5_relat_1(X0,X1),X2),k10_relat_1(X0,k10_relat_1(X1,k2_xboole_0(X2,X3)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f76,f35])).
% 1.64/0.58  fof(f76,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k10_relat_1(k5_relat_1(X0,X1),X2),k10_relat_1(X0,k10_relat_1(X1,k2_xboole_0(X2,X3)))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(superposition,[],[f66,f33])).
% 1.64/0.58  fof(f28,plain,(
% 1.64/0.58    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))),
% 1.64/0.58    inference(cnf_transformation,[],[f23])).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (18047)------------------------------
% 1.64/0.58  % (18047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (18047)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (18047)Memory used [KB]: 6780
% 1.64/0.58  % (18047)Time elapsed: 0.167 s
% 1.64/0.58  % (18047)------------------------------
% 1.64/0.58  % (18047)------------------------------
% 1.64/0.60  % (18042)Success in time 0.24 s
%------------------------------------------------------------------------------

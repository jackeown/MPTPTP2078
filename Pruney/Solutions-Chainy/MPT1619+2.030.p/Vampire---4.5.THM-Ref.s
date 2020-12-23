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
% DateTime   : Thu Dec  3 13:16:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 204 expanded)
%              Number of leaves         :   12 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  148 ( 795 expanded)
%              Number of equality atoms :   44 (  97 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65,f39])).

fof(f39,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f24,f38,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f65,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f64,f46])).

fof(f46,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f45,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f27,f25])).

fof(f25,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f45,plain,(
    ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0)) ),
    inference(resolution,[],[f41,f23])).

fof(f23,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f64,plain,(
    g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f63,f55])).

fof(f55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f30,f50])).

fof(f50,plain,(
    k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f49,f30])).

fof(f49,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f48,f31])).

fof(f31,plain,(
    ! [X0] : v4_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_yellow_1(sK1(X0))
      & v1_partfun1(sK1(X0),X0)
      & v1_funct_1(sK1(X0))
      & v4_relat_1(sK1(X0),X0)
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_yellow_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v1_yellow_1(sK1(X0))
        & v1_partfun1(sK1(X0),X0)
        & v1_funct_1(sK1(X0))
        & v4_relat_1(sK1(X0),X0)
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_yellow_1(X1)
      & v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).

fof(f48,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v1_funct_1(sK1(k1_xboole_0))
    | ~ v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X0] : v1_partfun1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_partfun1(X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_pboole)).

fof(f30,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,
    ( g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f62,f52])).

fof(f52,plain,(
    v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f31,f50])).

fof(f62,plain,
    ( g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f61,f54])).

fof(f54,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f32,f50])).

fof(f61,plain,
    ( g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f58,f51])).

fof(f51,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f33,f50])).

fof(f58,plain,
    ( g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f40,f53])).

fof(f53,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(superposition,[],[f34,f50])).

fof(f34,plain,(
    ! [X0] : v1_yellow_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_yellow_1(X0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f28,f38,f38])).

fof(f28,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (30769)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.44  % (30775)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.44  % (30775)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f65,f39])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.20/0.44    inference(definition_unfolding,[],[f24,f38,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f26,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 0.20/0.44    inference(forward_demodulation,[],[f64,f46])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.44    inference(superposition,[],[f45,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) )),
% 0.20/0.44    inference(resolution,[],[f27,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) )),
% 0.20/0.44    inference(resolution,[],[f41,f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    l1_orders_2(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f37,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f63,f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    v1_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(superposition,[],[f30,f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    k1_xboole_0 = sK1(k1_xboole_0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f49,f30])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    k1_xboole_0 = sK1(k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f48,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X0] : (v4_relat_1(sK1(X0),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0] : (v1_yellow_1(sK1(X0)) & v1_partfun1(sK1(X0),X0) & v1_funct_1(sK1(X0)) & v4_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0] : (? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_yellow_1(sK1(X0)) & v1_partfun1(sK1(X0),X0) & v1_funct_1(sK1(X0)) & v4_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0] : ? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_yellow_1)).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    k1_xboole_0 = sK1(k1_xboole_0) | ~v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f47,f32])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    k1_xboole_0 = sK1(k1_xboole_0) | ~v1_funct_1(sK1(k1_xboole_0)) | ~v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.20/0.44    inference(resolution,[],[f29,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X0] : (v1_partfun1(sK1(X0),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | k1_xboole_0 = X0 | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = X0 | (~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0] : ((v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k1_xboole_0 = X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_pboole)).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f62,f52])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.44    inference(superposition,[],[f31,f50])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f61,f54])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    v1_funct_1(k1_xboole_0)),
% 0.20/0.44    inference(superposition,[],[f32,f50])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f58,f51])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.44    inference(superposition,[],[f33,f50])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(resolution,[],[f40,f53])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    v1_yellow_1(k1_xboole_0)),
% 0.20/0.44    inference(superposition,[],[f34,f50])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0] : (v1_yellow_1(sK1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_yellow_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k6_partfun1(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f28,f38,f38])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (30775)------------------------------
% 0.20/0.44  % (30775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (30775)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (30775)Memory used [KB]: 6140
% 0.20/0.44  % (30775)Time elapsed: 0.007 s
% 0.20/0.44  % (30775)------------------------------
% 0.20/0.44  % (30775)------------------------------
% 0.20/0.45  % (30756)Success in time 0.089 s
%------------------------------------------------------------------------------

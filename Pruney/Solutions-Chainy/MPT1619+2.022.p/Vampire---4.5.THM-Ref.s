%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  92 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  141 ( 323 expanded)
%              Number of equality atoms :   42 (  54 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(subsumption_resolution,[],[f74,f42])).

fof(f42,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f26,f28,f28])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f74,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f73,f54])).

fof(f54,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f52,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f52,plain,(
    ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0)) ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f73,plain,(
    g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f72,f60])).

fof(f60,plain,(
    k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f59,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_yellow_1(sK1(X0))
      & v1_partfun1(sK1(X0),X0)
      & v1_funct_1(sK1(X0))
      & v4_relat_1(sK1(X0),X0)
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f23])).

fof(f23,plain,(
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

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_yellow_1(X1)
      & v1_partfun1(X1,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).

fof(f59,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f58,f35])).

fof(f35,plain,(
    ! [X0] : v4_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v1_funct_1(sK1(k1_xboole_0))
    | ~ v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X0] : v1_partfun1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_partfun1(X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).

fof(f72,plain,(
    g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f71,f34])).

fof(f71,plain,
    ( g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0))
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f70,f35])).

fof(f70,plain,
    ( g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0))
    | ~ v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f69,f36])).

fof(f69,plain,
    ( g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0))
    | ~ v1_funct_1(sK1(k1_xboole_0))
    | ~ v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X0] : v1_yellow_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,
    ( ~ v1_yellow_1(sK1(k1_xboole_0))
    | g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0))
    | ~ v1_funct_1(sK1(k1_xboole_0))
    | ~ v4_relat_1(sK1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f43,f37])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_yellow_1(X0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f32,f28,f28])).

fof(f32,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (21321)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.43  % (21321)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(subsumption_resolution,[],[f74,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.43    inference(definition_unfolding,[],[f26,f28,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.22/0.43    inference(negated_conjecture,[],[f11])).
% 0.22/0.43  fof(f11,conjecture,(
% 0.22/0.43    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.43    inference(forward_demodulation,[],[f73,f54])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.43    inference(superposition,[],[f52,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k2_funcop_1(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(resolution,[],[f31,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k2_funcop_1(X0,sK0))) )),
% 0.22/0.43    inference(resolution,[],[f44,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    l1_orders_2(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f22])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f41,f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,axiom,(
% 0.22/0.43    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.43    inference(forward_demodulation,[],[f72,f60])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    k1_xboole_0 = sK1(k1_xboole_0)),
% 0.22/0.43    inference(subsumption_resolution,[],[f59,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ! [X0] : (v1_yellow_1(sK1(X0)) & v1_partfun1(sK1(X0),X0) & v1_funct_1(sK1(X0)) & v4_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0)))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ! [X0] : (? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_yellow_1(sK1(X0)) & v1_partfun1(sK1(X0),X0) & v1_funct_1(sK1(X0)) & v4_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0] : ? [X1] : (v1_yellow_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    k1_xboole_0 = sK1(k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f58,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X0] : (v4_relat_1(sK1(X0),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    k1_xboole_0 = sK1(k1_xboole_0) | ~v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f57,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    k1_xboole_0 = sK1(k1_xboole_0) | ~v1_funct_1(sK1(k1_xboole_0)) | ~v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.22/0.43    inference(resolution,[],[f33,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0] : (v1_partfun1(sK1(X0),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | k1_xboole_0 = X0 | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0] : (k1_xboole_0 = X0 | (~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,axiom,(
% 0.22/0.43    ! [X0] : ((v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k1_xboole_0 = X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f71,f34])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0)) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f70,f35])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0)) | ~v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f69,f36])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0)) | ~v1_funct_1(sK1(k1_xboole_0)) | ~v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.22/0.43    inference(subsumption_resolution,[],[f67,f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    ( ! [X0] : (v1_yellow_1(sK1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    ~v1_yellow_1(sK1(k1_xboole_0)) | g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) = k5_yellow_1(k1_xboole_0,sK1(k1_xboole_0)) | ~v1_funct_1(sK1(k1_xboole_0)) | ~v4_relat_1(sK1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.22/0.43    inference(resolution,[],[f43,f37])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_partfun1(X0,k1_xboole_0) | ~v1_yellow_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k2_tarski(k1_xboole_0,k1_xboole_0),k6_partfun1(k2_tarski(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f32,f28,f28])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,axiom,(
% 0.22/0.43    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (21321)------------------------------
% 0.22/0.43  % (21321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (21321)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (21321)Memory used [KB]: 1663
% 0.22/0.43  % (21321)Time elapsed: 0.006 s
% 0.22/0.43  % (21321)------------------------------
% 0.22/0.43  % (21321)------------------------------
% 0.22/0.43  % (21307)Success in time 0.065 s
%------------------------------------------------------------------------------

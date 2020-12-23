%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 125 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 ( 288 expanded)
%              Number of equality atoms :   62 ( 109 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f114])).

fof(f114,plain,(
    ~ v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f113,f79])).

fof(f79,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f46,f50])).

fof(f50,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f46,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f113,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f112,f107])).

fof(f107,plain,(
    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f102,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f56,f80])).

fof(f80,plain,(
    ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f49,f63])).

fof(f63,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f49,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f102,plain,(
    ! [X0] : k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0)) ),
    inference(resolution,[],[f66,f45])).

fof(f45,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f112,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f111,f85])).

fof(f85,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f52,f48])).

fof(f48,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f111,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f110,f84])).

fof(f84,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f53,f48])).

fof(f53,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f109,f88])).

fof(f88,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f81,f48])).

fof(f81,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f54,f50])).

fof(f54,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f109,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f108,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_yellow_1(X0)
      | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f59,f50])).

fof(f59,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f108,plain,(
    v1_yellow_1(k1_xboole_0) ),
    inference(superposition,[],[f93,f90])).

fof(f93,plain,(
    ! [X0] : v1_yellow_1(k7_funcop_1(X0,sK0)) ),
    inference(resolution,[],[f83,f45])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | v1_yellow_1(k7_funcop_1(X0,X1)) ) ),
    inference(forward_demodulation,[],[f65,f63])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(f130,plain,(
    v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f115,f128])).

fof(f128,plain,(
    k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK1(X0) ) ),
    inference(superposition,[],[f95,f62])).

fof(f62,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_tarski(X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

fof(f95,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_relat_1(sK1(X1))
      | k1_xboole_0 = sK1(X1) ) ),
    inference(resolution,[],[f57,f60])).

fof(f60,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f115,plain,(
    ! [X0] : v4_relat_1(sK1(X0),X0) ),
    inference(resolution,[],[f100,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | v4_relat_1(sK1(X2),X3) ) ),
    inference(forward_demodulation,[],[f99,f62])).

fof(f99,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(sK1(X2)),X3)
      | v4_relat_1(sK1(X2),X3) ) ),
    inference(resolution,[],[f68,f60])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (24068)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.44  % (24060)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.45  % (24052)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.45  % (24052)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f136,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(subsumption_resolution,[],[f130,f114])).
% 0.19/0.46  fof(f114,plain,(
% 0.19/0.46    ~v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f113,f79])).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))),
% 0.19/0.46    inference(forward_demodulation,[],[f46,f50])).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f18,axiom,(
% 0.19/0.46    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f39])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f38])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f25])).
% 0.19/0.46  fof(f25,negated_conjecture,(
% 0.19/0.46    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.19/0.46    inference(negated_conjecture,[],[f24])).
% 0.19/0.46  fof(f24,conjecture,(
% 0.19/0.46    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.19/0.46  fof(f113,plain,(
% 0.19/0.46    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | ~v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.46    inference(forward_demodulation,[],[f112,f107])).
% 0.19/0.46  fof(f107,plain,(
% 0.19/0.46    k6_yellow_1(k1_xboole_0,sK0) = k5_yellow_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.46    inference(superposition,[],[f102,f90])).
% 0.19/0.46  fof(f90,plain,(
% 0.19/0.46    ( ! [X0] : (k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)) )),
% 0.19/0.46    inference(resolution,[],[f56,f80])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    ( ! [X0] : (v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f49,f63])).
% 0.19/0.46  fof(f63,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f22])).
% 0.19/0.46  fof(f22,axiom,(
% 0.19/0.46    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f21])).
% 0.19/0.46  fof(f21,axiom,(
% 0.19/0.46    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.19/0.46  fof(f56,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.46    inference(cnf_transformation,[],[f30])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.46  fof(f102,plain,(
% 0.19/0.46    ( ! [X0] : (k6_yellow_1(X0,sK0) = k5_yellow_1(X0,k7_funcop_1(X0,sK0))) )),
% 0.19/0.46    inference(resolution,[],[f66,f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    l1_orders_2(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f39])).
% 0.19/0.46  fof(f66,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~l1_orders_2(X1) | k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f19])).
% 0.19/0.46  fof(f19,axiom,(
% 0.19/0.46    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.19/0.46  fof(f112,plain,(
% 0.19/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f111,f85])).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    v1_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(superposition,[],[f52,f48])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(cnf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,axiom,(
% 0.19/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,axiom,(
% 0.19/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.46  fof(f111,plain,(
% 0.19/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f110,f84])).
% 0.19/0.46  fof(f84,plain,(
% 0.19/0.46    v1_funct_1(k1_xboole_0)),
% 0.19/0.46    inference(superposition,[],[f53,f48])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f110,plain,(
% 0.19/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f109,f88])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.46    inference(superposition,[],[f81,f48])).
% 0.19/0.46  fof(f81,plain,(
% 0.19/0.46    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f54,f50])).
% 0.19/0.46  fof(f54,plain,(
% 0.19/0.46    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ! [X0] : v1_partfun1(k6_partfun1(X0),X0)),
% 0.19/0.46    inference(pure_predicate_removal,[],[f17])).
% 0.19/0.46  fof(f17,axiom,(
% 0.19/0.46    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.19/0.46  fof(f109,plain,(
% 0.19/0.46    g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k5_yellow_1(k1_xboole_0,k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(resolution,[],[f108,f82])).
% 0.19/0.46  fof(f82,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_yellow_1(X0) | k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f59,f50])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f33])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f23])).
% 0.19/0.46  fof(f23,axiom,(
% 0.19/0.46    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.19/0.46  fof(f108,plain,(
% 0.19/0.46    v1_yellow_1(k1_xboole_0)),
% 0.19/0.46    inference(superposition,[],[f93,f90])).
% 0.19/0.46  fof(f93,plain,(
% 0.19/0.46    ( ! [X0] : (v1_yellow_1(k7_funcop_1(X0,sK0))) )),
% 0.19/0.46    inference(resolution,[],[f83,f45])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~l1_orders_2(X1) | v1_yellow_1(k7_funcop_1(X0,X1))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f65,f63])).
% 0.19/0.46  fof(f65,plain,(
% 0.19/0.46    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f20])).
% 0.19/0.46  fof(f20,axiom,(
% 0.19/0.46    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.19/0.46  fof(f130,plain,(
% 0.19/0.46    v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.19/0.46    inference(superposition,[],[f115,f128])).
% 0.19/0.46  fof(f128,plain,(
% 0.19/0.46    k1_xboole_0 = sK1(k1_xboole_0)),
% 0.19/0.46    inference(equality_resolution,[],[f117])).
% 0.19/0.46  fof(f117,plain,(
% 0.19/0.46    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK1(X0)) )),
% 0.19/0.46    inference(superposition,[],[f95,f62])).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.19/0.46    inference(cnf_transformation,[],[f41])).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    ! [X0] : (k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ! [X0] : (? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.19/0.46    inference(pure_predicate_removal,[],[f16])).
% 0.19/0.46  fof(f16,axiom,(
% 0.19/0.46    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_tarski(X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).
% 0.19/0.46  fof(f95,plain,(
% 0.19/0.46    ( ! [X1] : (k1_xboole_0 != k1_relat_1(sK1(X1)) | k1_xboole_0 = sK1(X1)) )),
% 0.19/0.46    inference(resolution,[],[f57,f60])).
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f41])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.19/0.46    inference(cnf_transformation,[],[f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(flattening,[],[f31])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f13])).
% 0.19/0.46  fof(f13,axiom,(
% 0.19/0.46    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.19/0.46  fof(f115,plain,(
% 0.19/0.46    ( ! [X0] : (v4_relat_1(sK1(X0),X0)) )),
% 0.19/0.46    inference(resolution,[],[f100,f77])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.46    inference(equality_resolution,[],[f70])).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.46    inference(cnf_transformation,[],[f44])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.46    inference(flattening,[],[f43])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.46    inference(nnf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.46  fof(f100,plain,(
% 0.19/0.46    ( ! [X2,X3] : (~r1_tarski(X2,X3) | v4_relat_1(sK1(X2),X3)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f99,f62])).
% 0.19/0.46  fof(f99,plain,(
% 0.19/0.46    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(sK1(X2)),X3) | v4_relat_1(sK1(X2),X3)) )),
% 0.19/0.46    inference(resolution,[],[f68,f60])).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f42])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(nnf_transformation,[],[f37])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,axiom,(
% 0.19/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (24052)------------------------------
% 0.19/0.46  % (24052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (24052)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (24052)Memory used [KB]: 1791
% 0.19/0.46  % (24052)Time elapsed: 0.058 s
% 0.19/0.46  % (24052)------------------------------
% 0.19/0.46  % (24052)------------------------------
% 0.19/0.46  % (24044)Success in time 0.112 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1619+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 114 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10665,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10664,f7002])).

fof(f7002,plain,(
    l1_orders_2(sK395) ),
    inference(cnf_transformation,[],[f5389])).

fof(f5389,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK395)
    & l1_orders_2(sK395) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK395])],[f3177,f5388])).

fof(f5388,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK395)
      & l1_orders_2(sK395) ) ),
    introduced(choice_axiom,[])).

fof(f3177,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3141])).

fof(f3141,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f3140])).

fof(f3140,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f10664,plain,(
    ~ l1_orders_2(sK395) ),
    inference(equality_resolution,[],[f10659])).

fof(f10659,plain,(
    ! [X1] :
      ( k6_yellow_1(k1_xboole_0,sK395) != k6_yellow_1(k1_xboole_0,X1)
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f10658,f8293])).

fof(f8293,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f3873])).

fof(f3873,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f3090])).

fof(f3090,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(f10658,plain,(
    ! [X1] :
      ( k6_yellow_1(k1_xboole_0,sK395) != k6_yellow_1(k1_xboole_0,X1)
      | ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f10657,f8373])).

fof(f8373,plain,(
    ! [X0,X1] : v1_relat_1(k2_funcop_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3094])).

fof(f3094,axiom,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funcop_1(X0,X1))
      & v1_relat_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_funcop_1)).

fof(f10657,plain,(
    ! [X1] :
      ( k6_yellow_1(k1_xboole_0,sK395) != k6_yellow_1(k1_xboole_0,X1)
      | ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f10656,f8375])).

fof(f8375,plain,(
    ! [X0,X1] : v4_relat_1(k2_funcop_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3093])).

fof(f3093,axiom,(
    ! [X0,X1] : v4_relat_1(k2_funcop_1(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_funcop_1)).

fof(f10656,plain,(
    ! [X1] :
      ( k6_yellow_1(k1_xboole_0,sK395) != k6_yellow_1(k1_xboole_0,X1)
      | ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ v4_relat_1(k2_funcop_1(k1_xboole_0,X1),k1_xboole_0)
      | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f10655,f8374])).

fof(f8374,plain,(
    ! [X0,X1] : v1_funct_1(k2_funcop_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3094])).

fof(f10655,plain,(
    ! [X1] :
      ( k6_yellow_1(k1_xboole_0,sK395) != k6_yellow_1(k1_xboole_0,X1)
      | ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ v1_funct_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ v4_relat_1(k2_funcop_1(k1_xboole_0,X1),k1_xboole_0)
      | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f10649,f8372])).

fof(f8372,plain,(
    ! [X0,X1] : v1_partfun1(k2_funcop_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3097])).

fof(f3097,axiom,(
    ! [X0,X1] :
      ( v1_partfun1(k2_funcop_1(X0,X1),X0)
      & v1_funct_1(k2_funcop_1(X0,X1))
      & v4_relat_1(k2_funcop_1(X0,X1),X0)
      & v1_relat_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc20_funcop_1)).

fof(f10649,plain,(
    ! [X1] :
      ( k6_yellow_1(k1_xboole_0,sK395) != k6_yellow_1(k1_xboole_0,X1)
      | ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ v1_partfun1(k2_funcop_1(k1_xboole_0,X1),k1_xboole_0)
      | ~ v1_funct_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ v4_relat_1(k2_funcop_1(k1_xboole_0,X1),k1_xboole_0)
      | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(superposition,[],[f10533,f9961])).

fof(f9961,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(definition_unfolding,[],[f7006,f7145])).

fof(f7145,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f3119])).

fof(f3119,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f7006,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f3179])).

fof(f3179,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f3078])).

fof(f3078,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f10533,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) != k6_yellow_1(k1_xboole_0,sK395)
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f7003,f7141])).

fof(f7141,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3266])).

fof(f3266,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3265])).

fof(f3265,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3139])).

fof(f3139,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f7003,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK395) ),
    inference(cnf_transformation,[],[f5389])).
%------------------------------------------------------------------------------

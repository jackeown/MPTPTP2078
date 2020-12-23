%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:01 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 182 expanded)
%              Number of leaves         :   17 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  458 (1154 expanded)
%              Number of equality atoms :  218 ( 218 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(subsumption_resolution,[],[f123,f104])).

fof(f104,plain,(
    r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[],[f82,f103])).

fof(f103,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f102,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

fof(f102,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f98])).

fof(f98,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f101,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f99,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f99,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f80,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f70,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X10,X5,X3,X1] : r2_hidden(X10,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X10)) ),
    inference(equality_resolution,[],[f81])).

% (6315)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (6316)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f81,plain,(
    ! [X6,X4,X2,X0,X10,X8,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X10) != X8 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | X7 != X10
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ( ( ( sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(f123,plain,(
    ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f122,f43])).

fof(f43,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f122,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f121,f42])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f120,f42])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
      | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),X1)) ) ),
    inference(subsumption_resolution,[],[f119,f37])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f38])).

fof(f38,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f41])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f116,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

% (6326)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f115,f37])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f38])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f39])).

fof(f39,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f41])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f40])).

fof(f40,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,k2_orders_2(X0,X2))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:06:49 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.49  % (6308)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.49  % (6305)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.50  % (6317)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.50  % (6328)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.50  % (6322)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.18/0.50  % (6327)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.18/0.51  % (6330)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.51  % (6312)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.51  % (6325)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.51  % (6308)Refutation found. Thanks to Tanya!
% 0.18/0.51  % SZS status Theorem for theBenchmark
% 0.18/0.51  % SZS output start Proof for theBenchmark
% 0.18/0.51  fof(f124,plain,(
% 0.18/0.51    $false),
% 0.18/0.51    inference(subsumption_resolution,[],[f123,f104])).
% 0.18/0.51  fof(f104,plain,(
% 0.18/0.51    r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.18/0.51    inference(superposition,[],[f82,f103])).
% 0.18/0.51  fof(f103,plain,(
% 0.18/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.18/0.51    inference(subsumption_resolution,[],[f102,f37])).
% 0.18/0.51  fof(f37,plain,(
% 0.18/0.51    ~v2_struct_0(sK0)),
% 0.18/0.51    inference(cnf_transformation,[],[f31])).
% 0.18/0.51  fof(f31,plain,(
% 0.18/0.51    (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f30,f29])).
% 0.18/0.51  fof(f29,plain,(
% 0.18/0.51    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f30,plain,(
% 0.18/0.51    ? [X1] : (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) => (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f18,plain,(
% 0.18/0.51    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.18/0.51    inference(flattening,[],[f17])).
% 0.18/0.51  fof(f17,plain,(
% 0.18/0.51    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f15])).
% 0.18/0.51  fof(f15,negated_conjecture,(
% 0.18/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.18/0.51    inference(negated_conjecture,[],[f14])).
% 0.18/0.51  fof(f14,conjecture,(
% 0.18/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).
% 0.18/0.51  fof(f102,plain,(
% 0.18/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | v2_struct_0(sK0)),
% 0.18/0.51    inference(subsumption_resolution,[],[f101,f98])).
% 0.18/0.51  fof(f98,plain,(
% 0.18/0.51    l1_struct_0(sK0)),
% 0.18/0.51    inference(resolution,[],[f66,f41])).
% 0.18/0.51  fof(f41,plain,(
% 0.18/0.51    l1_orders_2(sK0)),
% 0.18/0.51    inference(cnf_transformation,[],[f31])).
% 0.18/0.51  fof(f66,plain,(
% 0.18/0.51    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f28])).
% 0.18/0.51  fof(f28,plain,(
% 0.18/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.18/0.51    inference(ennf_transformation,[],[f10])).
% 0.18/0.51  fof(f10,axiom,(
% 0.18/0.51    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.18/0.51  fof(f101,plain,(
% 0.18/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.18/0.51    inference(resolution,[],[f99,f65])).
% 0.18/0.51  fof(f65,plain,(
% 0.18/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f27])).
% 0.18/0.51  fof(f27,plain,(
% 0.18/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.51    inference(flattening,[],[f26])).
% 0.18/0.51  fof(f26,plain,(
% 0.18/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f9])).
% 0.18/0.51  fof(f9,axiom,(
% 0.18/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.18/0.51  fof(f99,plain,(
% 0.18/0.51    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.18/0.51    inference(resolution,[],[f80,f42])).
% 0.18/0.51  fof(f42,plain,(
% 0.18/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.18/0.51    inference(cnf_transformation,[],[f31])).
% 0.18/0.51  fof(f80,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f63,f79])).
% 0.18/0.51  fof(f79,plain,(
% 0.18/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f68,f78])).
% 0.18/0.51  fof(f78,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f70,f77])).
% 0.18/0.51  fof(f77,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f72,f76])).
% 0.18/0.51  fof(f76,plain,(
% 0.18/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f73,f75])).
% 0.18/0.51  fof(f75,plain,(
% 0.18/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f71,f74])).
% 0.18/0.51  fof(f74,plain,(
% 0.18/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.51    inference(definition_unfolding,[],[f69,f67])).
% 0.18/0.51  fof(f67,plain,(
% 0.18/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f7])).
% 0.18/0.51  fof(f7,axiom,(
% 0.18/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.18/0.51  fof(f69,plain,(
% 0.18/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f6])).
% 0.18/0.51  fof(f6,axiom,(
% 0.18/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.18/0.51  fof(f71,plain,(
% 0.18/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f5])).
% 0.18/0.51  fof(f5,axiom,(
% 0.18/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.18/0.51  fof(f73,plain,(
% 0.18/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f4])).
% 0.18/0.51  fof(f4,axiom,(
% 0.18/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.18/0.51  fof(f72,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f3])).
% 0.18/0.51  fof(f3,axiom,(
% 0.18/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.51  fof(f70,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f2])).
% 0.18/0.51  fof(f2,axiom,(
% 0.18/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.51  fof(f68,plain,(
% 0.18/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f1])).
% 0.18/0.51  fof(f1,axiom,(
% 0.18/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.51  fof(f63,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f23])).
% 0.18/0.51  fof(f23,plain,(
% 0.18/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.18/0.51    inference(flattening,[],[f22])).
% 0.18/0.51  fof(f22,plain,(
% 0.18/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f11])).
% 0.18/0.51  fof(f11,axiom,(
% 0.18/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.18/0.51  fof(f82,plain,(
% 0.18/0.51    ( ! [X6,X4,X2,X0,X10,X5,X3,X1] : (r2_hidden(X10,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X10))) )),
% 0.18/0.51    inference(equality_resolution,[],[f81])).
% 0.18/0.51  % (6315)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.51  % (6316)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.51  fof(f81,plain,(
% 0.18/0.51    ( ! [X6,X4,X2,X0,X10,X8,X5,X3,X1] : (r2_hidden(X10,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X10) != X8) )),
% 0.18/0.51    inference(equality_resolution,[],[f52])).
% 0.18/0.51  fof(f52,plain,(
% 0.18/0.51    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | X7 != X10 | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.18/0.51    inference(cnf_transformation,[],[f36])).
% 0.18/0.51  fof(f36,plain,(
% 0.18/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | (((sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.18/0.51  fof(f35,plain,(
% 0.18/0.51    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8))) => (((sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f34,plain,(
% 0.18/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.18/0.51    inference(rectify,[],[f33])).
% 0.18/0.51  fof(f33,plain,(
% 0.18/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.18/0.51    inference(flattening,[],[f32])).
% 0.18/0.51  fof(f32,plain,(
% 0.18/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~r2_hidden(X9,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.18/0.51    inference(nnf_transformation,[],[f19])).
% 0.18/0.51  fof(f19,plain,(
% 0.18/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 0.18/0.51    inference(ennf_transformation,[],[f8])).
% 0.18/0.51  fof(f8,axiom,(
% 0.18/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).
% 0.18/0.51  fof(f123,plain,(
% 0.18/0.51    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.18/0.51    inference(subsumption_resolution,[],[f122,f43])).
% 0.18/0.51  fof(f43,plain,(
% 0.18/0.51    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.18/0.51    inference(cnf_transformation,[],[f31])).
% 0.18/0.51  fof(f122,plain,(
% 0.18/0.51    ~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.18/0.51    inference(resolution,[],[f121,f42])).
% 0.18/0.51  fof(f121,plain,(
% 0.18/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1))) )),
% 0.18/0.51    inference(resolution,[],[f120,f42])).
% 0.18/0.51  fof(f120,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),X1))) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f119,f37])).
% 0.18/0.51  fof(f119,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f118,f38])).
% 0.18/0.51  fof(f38,plain,(
% 0.18/0.51    v3_orders_2(sK0)),
% 0.18/0.51    inference(cnf_transformation,[],[f31])).
% 0.18/0.51  fof(f118,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f117,f41])).
% 0.18/0.51  fof(f117,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.18/0.51    inference(resolution,[],[f116,f64])).
% 0.18/0.51  fof(f64,plain,(
% 0.18/0.51    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f25])).
% 0.18/0.51  fof(f25,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.18/0.51    inference(flattening,[],[f24])).
% 0.18/0.51  % (6326)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f16])).
% 0.18/0.51  fof(f16,plain,(
% 0.18/0.51    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.18/0.51    inference(pure_predicate_removal,[],[f12])).
% 0.18/0.51  fof(f12,axiom,(
% 0.18/0.51    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
% 0.18/0.51  fof(f116,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,X1))) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f115,f37])).
% 0.18/0.51  fof(f115,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | v2_struct_0(sK0)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f114,f38])).
% 0.18/0.51  fof(f114,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f113,f39])).
% 0.18/0.51  fof(f39,plain,(
% 0.18/0.51    v4_orders_2(sK0)),
% 0.18/0.51    inference(cnf_transformation,[],[f31])).
% 0.18/0.51  fof(f113,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f112,f41])).
% 0.18/0.51  fof(f112,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.18/0.51    inference(resolution,[],[f62,f40])).
% 0.18/0.51  fof(f40,plain,(
% 0.18/0.51    v5_orders_2(sK0)),
% 0.18/0.51    inference(cnf_transformation,[],[f31])).
% 0.18/0.51  fof(f62,plain,(
% 0.18/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X1,k2_orders_2(X0,X2)) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f21])).
% 0.18/0.51  fof(f21,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.18/0.51    inference(flattening,[],[f20])).
% 0.18/0.51  fof(f20,plain,(
% 0.18/0.51    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f13])).
% 0.18/0.51  fof(f13,axiom,(
% 0.18/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
% 0.18/0.51  % SZS output end Proof for theBenchmark
% 0.18/0.51  % (6308)------------------------------
% 0.18/0.51  % (6308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (6308)Termination reason: Refutation
% 0.18/0.51  
% 0.18/0.51  % (6308)Memory used [KB]: 6396
% 0.18/0.51  % (6308)Time elapsed: 0.114 s
% 0.18/0.51  % (6308)------------------------------
% 0.18/0.51  % (6308)------------------------------
% 0.18/0.51  % (6306)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.51  % (6304)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.51  % (6307)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.52  % (6302)Success in time 0.178 s
%------------------------------------------------------------------------------

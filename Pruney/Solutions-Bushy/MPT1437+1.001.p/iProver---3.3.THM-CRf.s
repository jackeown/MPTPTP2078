%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1437+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:41 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  139 (5362 expanded)
%              Number of clauses        :   86 (1209 expanded)
%              Number of leaves         :   12 (1416 expanded)
%              Depth                    :   31
%              Number of atoms          :  539 (34772 expanded)
%              Number of equality atoms :  218 (1968 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
                <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <~> r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <~> r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & ( r3_lattices(X0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & ( r3_lattices(X0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattices(X0,X1,X2)
            | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
          & ( r3_lattices(X0,X1,X2)
            | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r3_lattices(X0,X1,sK4)
          | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,sK4),k8_filter_1(X0)) )
        & ( r3_lattices(X0,X1,sK4)
          | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,sK4),k8_filter_1(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & ( r3_lattices(X0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r3_lattices(X0,sK3,X2)
              | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),sK3,X2),k8_filter_1(X0)) )
            & ( r3_lattices(X0,sK3,X2)
              | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),sK3,X2),k8_filter_1(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,X1,X2)
                  | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
                & ( r3_lattices(X0,X1,X2)
                  | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK2,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),X1,X2),k8_filter_1(sK2)) )
              & ( r3_lattices(sK2,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),X1,X2),k8_filter_1(sK2)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l3_lattices(sK2)
      & v10_lattices(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r3_lattices(sK2,sK3,sK4)
      | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) )
    & ( r3_lattices(sK2,sK3,sK4)
      | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).

fof(f49,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( r3_lattices(sK2,sK3,sK4)
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,
    ( ~ r3_lattices(sK2,sK3,sK4)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,a_1_0_filter_1(X1))
          | ! [X2,X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
        & ( ? [X2,X3] :
              ( r3_lattices(X1,X2,X3)
              & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
              & m1_subset_1(X3,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,a_1_0_filter_1(X1))
          | ! [X2,X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
        & ( ? [X4,X5] :
              ( r3_lattices(X1,X4,X5)
              & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X4,X5) = X0
              & m1_subset_1(X5,u1_struct_0(X1))
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4,X5] :
          ( r3_lattices(X1,X4,X5)
          & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X4,X5) = X0
          & m1_subset_1(X5,u1_struct_0(X1))
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,sK0(X0,X1),sK1(X0,X1))
        & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK0(X0,X1),sK1(X0,X1)) = X0
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X1))
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,a_1_0_filter_1(X1))
          | ! [X2,X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,sK0(X0,X1),sK1(X0,X1))
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK0(X0,X1),sK1(X0,X1)) = X0
            & m1_subset_1(sK1(X0,X1),u1_struct_0(X1))
            & m1_subset_1(sK0(X0,X1),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ r3_lattices(X1,X2,X3)
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),a_1_0_filter_1(X1))
      | ~ r3_lattices(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK0(X0,X1),sK1(X0,X1)) = X0
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r3_lattices(X1,sK0(X0,X1),sK1(X0,X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_684,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_685,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | k1_domain_1(X3,X1,X2,X0) = k4_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_688,plain,
    ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1505,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK4) = k4_tarski(X1,sK4)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_688])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,plain,
    ( l3_lattices(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_45,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_47,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_2,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_48,plain,
    ( l1_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_50,plain,
    ( l1_lattices(sK2) = iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_1,plain,
    ( ~ l1_lattices(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_51,plain,
    ( l1_lattices(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_53,plain,
    ( l1_lattices(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_1680,plain,
    ( v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | k1_domain_1(X0,u1_struct_0(sK2),X1,sK4) = k4_tarski(X1,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1505,c_19,c_21,c_47,c_50,c_53])).

cnf(c_1681,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK4) = k4_tarski(X1,sK4)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1680])).

cnf(c_1691,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4) = k4_tarski(sK3,sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_1681])).

cnf(c_46,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_49,plain,
    ( l1_lattices(sK2)
    | ~ l3_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_52,plain,
    ( ~ l1_lattices(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_920,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(u1_struct_0(sK2))
    | k1_domain_1(u1_struct_0(sK2),X1,sK3,X0) = k4_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4) = k4_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_2151,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4) = k4_tarski(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1691,c_18,c_16,c_15,c_14,c_46,c_49,c_52,c_1011])).

cnf(c_13,negated_conjecture,
    ( r3_lattices(sK2,sK3,sK4)
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_686,plain,
    ( r3_lattices(sK2,sK3,sK4) = iProver_top
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2154,plain,
    ( r3_lattices(sK2,sK3,sK4) = iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),k8_filter_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2151,c_686])).

cnf(c_12,negated_conjecture,
    ( ~ r3_lattices(sK2,sK3,sK4)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_687,plain,
    ( r3_lattices(sK2,sK3,sK4) != iProver_top
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2155,plain,
    ( r3_lattices(sK2,sK3,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),k8_filter_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2151,c_687])).

cnf(c_17,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,plain,
    ( v10_lattices(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_23,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),a_1_0_filter_1(X0))
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_693,plain,
    ( r3_lattices(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),a_1_0_filter_1(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2166,plain,
    ( r3_lattices(sK2,sK3,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),a_1_0_filter_1(sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v10_lattices(sK2) != iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2151,c_693])).

cnf(c_682,plain,
    ( v10_lattices(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0)
    | a_1_0_filter_1(X0) = k8_filter_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_697,plain,
    ( a_1_0_filter_1(X0) = k8_filter_1(X0)
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1355,plain,
    ( a_1_0_filter_1(sK2) = k8_filter_1(sK2)
    | v2_struct_0(sK2) = iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_682,c_697])).

cnf(c_55,plain,
    ( v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | ~ l3_lattices(sK2)
    | a_1_0_filter_1(sK2) = k8_filter_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1495,plain,
    ( a_1_0_filter_1(sK2) = k8_filter_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1355,c_18,c_17,c_16,c_55])).

cnf(c_2167,plain,
    ( r3_lattices(sK2,sK3,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),k8_filter_1(sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v10_lattices(sK2) != iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2166,c_1495])).

cnf(c_2170,plain,
    ( r3_lattices(sK2,sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2155,c_19,c_20,c_21,c_22,c_23,c_2167])).

cnf(c_2248,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),k8_filter_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2154,c_19,c_20,c_21,c_22,c_23,c_2155,c_2167])).

cnf(c_8,plain,
    ( m1_subset_1(sK0(X0,X1),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_1_0_filter_1(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_689,plain,
    ( m1_subset_1(sK0(X0,X1),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X0,a_1_0_filter_1(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v10_lattices(X1) != iProver_top
    | l3_lattices(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( m1_subset_1(sK1(X0,X1),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_1_0_filter_1(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_690,plain,
    ( m1_subset_1(sK1(X0,X1),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X0,a_1_0_filter_1(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v10_lattices(X1) != iProver_top
    | l3_lattices(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1723,plain,
    ( k1_domain_1(X0,u1_struct_0(X1),X2,sK1(X3,X1)) = k4_tarski(X2,sK1(X3,X1))
    | m1_subset_1(X2,X0) != iProver_top
    | r2_hidden(X3,a_1_0_filter_1(X1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v10_lattices(X1) != iProver_top
    | l3_lattices(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_688])).

cnf(c_5050,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK1(X2,sK2)) = k4_tarski(X1,sK1(X2,sK2))
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X2,k8_filter_1(sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v10_lattices(sK2) != iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_1723])).

cnf(c_8055,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK1(X2,sK2)) = k4_tarski(X1,sK1(X2,sK2))
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X2,k8_filter_1(sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5050,c_19,c_20,c_21,c_47,c_50,c_53])).

cnf(c_8067,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(X1,sK1(k4_tarski(sK3,sK4),sK2))
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_8055])).

cnf(c_8160,plain,
    ( k1_domain_1(u1_struct_0(X0),u1_struct_0(sK2),sK0(X1,X0),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(X1,X0),sK1(k4_tarski(sK3,sK4),sK2))
    | r2_hidden(X1,a_1_0_filter_1(X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_689,c_8067])).

cnf(c_1065,plain,
    ( l1_struct_0(X0)
    | ~ l3_lattices(X0) ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_1066,plain,
    ( l1_struct_0(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(c_11939,plain,
    ( r2_hidden(X1,a_1_0_filter_1(X0)) != iProver_top
    | k1_domain_1(u1_struct_0(X0),u1_struct_0(sK2),sK0(X1,X0),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(X1,X0),sK1(k4_tarski(sK3,sK4),sK2))
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8160,c_45,c_1066])).

cnf(c_11940,plain,
    ( k1_domain_1(u1_struct_0(X0),u1_struct_0(sK2),sK0(X1,X0),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(X1,X0),sK1(k4_tarski(sK3,sK4),sK2))
    | r2_hidden(X1,a_1_0_filter_1(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11939])).

cnf(c_11951,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2))
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v10_lattices(sK2) != iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_11940])).

cnf(c_13187,plain,
    ( r2_hidden(X0,k8_filter_1(sK2)) != iProver_top
    | k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11951,c_19,c_20,c_21])).

cnf(c_13188,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2))
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13187])).

cnf(c_13197,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(k4_tarski(sK3,sK4),sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(k4_tarski(sK3,sK4),sK2),sK1(k4_tarski(sK3,sK4),sK2)) ),
    inference(superposition,[status(thm)],[c_2248,c_13188])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,a_1_0_filter_1(X1))
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK0(X0,X1),sK1(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_691,plain,
    ( k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),sK0(X1,X0),sK1(X1,X0)) = X1
    | r2_hidden(X1,a_1_0_filter_1(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1881,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(X0,sK2)) = X0
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v10_lattices(sK2) != iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1495,c_691])).

cnf(c_2616,plain,
    ( r2_hidden(X0,k8_filter_1(sK2)) != iProver_top
    | k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(X0,sK2)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1881,c_19,c_20,c_21])).

cnf(c_2617,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(X0,sK2)) = X0
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2616])).

cnf(c_2624,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(k4_tarski(sK3,sK4),sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2248,c_2617])).

cnf(c_13237,plain,
    ( k4_tarski(sK0(k4_tarski(sK3,sK4),sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_13197,c_2624])).

cnf(c_11,plain,
    ( X0 = X1
    | k4_tarski(X1,X2) != k4_tarski(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14434,plain,
    ( k4_tarski(X0,X1) != k4_tarski(sK3,sK4)
    | sK0(k4_tarski(sK3,sK4),sK2) = X0 ),
    inference(superposition,[status(thm)],[c_13237,c_11])).

cnf(c_14864,plain,
    ( sK0(k4_tarski(sK3,sK4),sK2) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_14434])).

cnf(c_5,plain,
    ( r3_lattices(X0,sK0(X1,X0),sK1(X1,X0))
    | ~ r2_hidden(X1,a_1_0_filter_1(X0))
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_692,plain,
    ( r3_lattices(X0,sK0(X1,X0),sK1(X1,X0)) = iProver_top
    | r2_hidden(X1,a_1_0_filter_1(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v10_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15337,plain,
    ( r3_lattices(sK2,sK3,sK1(k4_tarski(sK3,sK4),sK2)) = iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),a_1_0_filter_1(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v10_lattices(sK2) != iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14864,c_692])).

cnf(c_10,plain,
    ( X0 = X1
    | k4_tarski(X2,X1) != k4_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14432,plain,
    ( k4_tarski(X0,X1) != k4_tarski(sK3,sK4)
    | sK1(k4_tarski(sK3,sK4),sK2) = X1 ),
    inference(superposition,[status(thm)],[c_13237,c_10])).

cnf(c_14853,plain,
    ( sK1(k4_tarski(sK3,sK4),sK2) = sK4 ),
    inference(equality_resolution,[status(thm)],[c_14432])).

cnf(c_15343,plain,
    ( r3_lattices(sK2,sK3,sK4) = iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),k8_filter_1(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v10_lattices(sK2) != iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15337,c_1495,c_14853])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15343,c_2170,c_2154,c_21,c_20,c_19])).


%------------------------------------------------------------------------------

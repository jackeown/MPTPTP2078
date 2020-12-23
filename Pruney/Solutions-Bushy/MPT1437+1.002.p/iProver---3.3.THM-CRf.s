%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1437+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  149 (3354 expanded)
%              Number of clauses        :   96 ( 704 expanded)
%              Number of leaves         :   12 ( 908 expanded)
%              Depth                    :   28
%              Number of atoms          :  557 (22900 expanded)
%              Number of equality atoms :  159 (1018 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f47,plain,
    ( ( ~ r3_lattices(sK2,sK3,sK4)
      | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) )
    & ( r3_lattices(sK2,sK3,sK4)
      | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l3_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f43,f46,f45,f44])).

fof(f70,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( r3_lattices(sK2,sK3,sK4)
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f40])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ r3_lattices(X1,X2,X3)
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),a_1_0_filter_1(X1))
      | ~ r3_lattices(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f68,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK0(X0,X1),sK1(X0,X1)) = X0
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,
    ( ~ r3_lattices(sK2,sK3,sK4)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r3_lattices(X1,sK0(X0,X1),sK1(X0,X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1081,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1082,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | k1_domain_1(X3,X1,X2,X0) = k4_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1085,plain,
    ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2224,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK4) = k4_tarski(X1,sK4)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1085])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,plain,
    ( l3_lattices(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_61,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_63,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_6,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_64,plain,
    ( l2_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_66,plain,
    ( l2_lattices(sK2) = iProver_top
    | l3_lattices(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_5,plain,
    ( ~ l2_lattices(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_67,plain,
    ( l2_lattices(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_69,plain,
    ( l2_lattices(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_2676,plain,
    ( v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | k1_domain_1(X0,u1_struct_0(sK2),X1,sK4) = k4_tarski(X1,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2224,c_26,c_28,c_63,c_66,c_69])).

cnf(c_2677,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK4) = k4_tarski(X1,sK4)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2676])).

cnf(c_2686,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4) = k4_tarski(sK3,sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_2677])).

cnf(c_62,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_65,plain,
    ( l2_lattices(sK2)
    | ~ l3_lattices(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_68,plain,
    ( ~ l2_lattices(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1256,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(u1_struct_0(sK2))
    | k1_domain_1(X1,u1_struct_0(sK2),X0,sK4) = k4_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1373,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4) = k4_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_2839,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4) = k4_tarski(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2686,c_25,c_23,c_22,c_21,c_62,c_65,c_68,c_1373])).

cnf(c_20,negated_conjecture,
    ( r3_lattices(sK2,sK3,sK4)
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_184,plain,
    ( r3_lattices(sK2,sK3,sK4)
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_8,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),a_1_0_filter_1(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_426,plain,
    ( ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),a_1_0_filter_1(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_427,plain,
    ( ~ r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),X0,X1),a_1_0_filter_1(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_431,plain,
    ( ~ r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),X0,X1),a_1_0_filter_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_25,c_23])).

cnf(c_432,plain,
    ( ~ r3_lattices(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),X0,X1),a_1_0_filter_1(sK2)) ),
    inference(renaming,[status(thm)],[c_431])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),X1,X0),a_1_0_filter_1(sK2))
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2))
    | sK4 != X0
    | sK3 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_432])).

cnf(c_590,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),a_1_0_filter_1(sK2))
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_592,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),a_1_0_filter_1(sK2))
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_590,c_22,c_21])).

cnf(c_1074,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),a_1_0_filter_1(sK2)) = iProver_top
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_4,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | a_1_0_filter_1(X0) = k8_filter_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_450,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | a_1_0_filter_1(X0) = k8_filter_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_451,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | a_1_0_filter_1(sK2) = k8_filter_1(sK2) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_71,plain,
    ( ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2)
    | a_1_0_filter_1(sK2) = k8_filter_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_453,plain,
    ( a_1_0_filter_1(sK2) = k8_filter_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_25,c_24,c_23,c_71])).

cnf(c_1153,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1074,c_453])).

cnf(c_2843,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),k8_filter_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2839,c_1153])).

cnf(c_12,plain,
    ( m1_subset_1(sK0(X0,X1),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_1_0_filter_1(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_458,plain,
    ( m1_subset_1(sK0(X0,X1),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_1_0_filter_1(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_459,plain,
    ( m1_subset_1(sK0(X0,sK2),u1_struct_0(sK2))
    | ~ r2_hidden(X0,a_1_0_filter_1(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_463,plain,
    ( m1_subset_1(sK0(X0,sK2),u1_struct_0(sK2))
    | ~ r2_hidden(X0,a_1_0_filter_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_25,c_23])).

cnf(c_1080,plain,
    ( m1_subset_1(sK0(X0,sK2),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,a_1_0_filter_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_1119,plain,
    ( m1_subset_1(sK0(X0,sK2),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1080,c_453])).

cnf(c_11,plain,
    ( m1_subset_1(sK1(X0,X1),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_1_0_filter_1(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_476,plain,
    ( m1_subset_1(sK1(X0,X1),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_1_0_filter_1(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_477,plain,
    ( m1_subset_1(sK1(X0,sK2),u1_struct_0(sK2))
    | ~ r2_hidden(X0,a_1_0_filter_1(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_481,plain,
    ( m1_subset_1(sK1(X0,sK2),u1_struct_0(sK2))
    | ~ r2_hidden(X0,a_1_0_filter_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_25,c_23])).

cnf(c_1079,plain,
    ( m1_subset_1(sK1(X0,sK2),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,a_1_0_filter_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_1114,plain,
    ( m1_subset_1(sK1(X0,sK2),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1079,c_453])).

cnf(c_2227,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK1(X2,sK2)) = k4_tarski(X1,sK1(X2,sK2))
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X2,k8_filter_1(sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1085])).

cnf(c_3727,plain,
    ( v1_xboole_0(X0) = iProver_top
    | r2_hidden(X2,k8_filter_1(sK2)) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | k1_domain_1(X0,u1_struct_0(sK2),X1,sK1(X2,sK2)) = k4_tarski(X1,sK1(X2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2227,c_26,c_28,c_63,c_66,c_69])).

cnf(c_3728,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK1(X2,sK2)) = k4_tarski(X1,sK1(X2,sK2))
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X2,k8_filter_1(sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3727])).

cnf(c_3769,plain,
    ( k1_domain_1(X0,u1_struct_0(sK2),X1,sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(X1,sK1(k4_tarski(sK3,sK4),sK2))
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_3728])).

cnf(c_5918,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2))
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_3769])).

cnf(c_8629,plain,
    ( r2_hidden(X0,k8_filter_1(sK2)) != iProver_top
    | k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5918,c_26,c_28,c_63,c_66,c_69])).

cnf(c_8630,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(X0,sK2),sK1(k4_tarski(sK3,sK4),sK2))
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8629])).

cnf(c_8640,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(k4_tarski(sK3,sK4),sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK0(k4_tarski(sK3,sK4),sK2),sK1(k4_tarski(sK3,sK4),sK2)) ),
    inference(superposition,[status(thm)],[c_2843,c_8630])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,a_1_0_filter_1(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK0(X0,X1),sK1(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_494,plain,
    ( ~ r2_hidden(X0,a_1_0_filter_1(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK0(X0,X1),sK1(X0,X1)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_495,plain,
    ( ~ r2_hidden(X0,a_1_0_filter_1(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2)
    | k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(X0,sK2)) = X0 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_499,plain,
    ( ~ r2_hidden(X0,a_1_0_filter_1(sK2))
    | k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(X0,sK2)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_25,c_23])).

cnf(c_1078,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(X0,sK2)) = X0
    | r2_hidden(X0,a_1_0_filter_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_1130,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(X0,sK2),sK1(X0,sK2)) = X0
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1078,c_453])).

cnf(c_1411,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),sK2),sK1(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),sK2)) = k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1153,c_1130])).

cnf(c_2842,plain,
    ( k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK0(k4_tarski(sK3,sK4),sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2839,c_1411])).

cnf(c_8645,plain,
    ( k4_tarski(sK0(k4_tarski(sK3,sK4),sK2),sK1(k4_tarski(sK3,sK4),sK2)) = k4_tarski(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_8640,c_2842])).

cnf(c_16,plain,
    ( X0 = X1
    | k4_tarski(X2,X1) != k4_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8722,plain,
    ( k4_tarski(X0,X1) != k4_tarski(sK3,sK4)
    | sK1(k4_tarski(sK3,sK4),sK2) = X1 ),
    inference(superposition,[status(thm)],[c_8645,c_16])).

cnf(c_8739,plain,
    ( sK1(k4_tarski(sK3,sK4),sK2) = sK4 ),
    inference(equality_resolution,[status(thm)],[c_8722])).

cnf(c_19,negated_conjecture,
    ( ~ r3_lattices(sK2,sK3,sK4)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_182,plain,
    ( ~ r3_lattices(sK2,sK3,sK4)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( r3_lattices(X0,sK0(X1,X0),sK1(X1,X0))
    | ~ r2_hidden(X1,a_1_0_filter_1(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_408,plain,
    ( r3_lattices(X0,sK0(X1,X0),sK1(X1,X0))
    | ~ r2_hidden(X1,a_1_0_filter_1(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_409,plain,
    ( r3_lattices(sK2,sK0(X0,sK2),sK1(X0,sK2))
    | ~ r2_hidden(X0,a_1_0_filter_1(sK2))
    | ~ l3_lattices(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_413,plain,
    ( r3_lattices(sK2,sK0(X0,sK2),sK1(X0,sK2))
    | ~ r2_hidden(X0,a_1_0_filter_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_25,c_23])).

cnf(c_569,plain,
    ( ~ r2_hidden(X0,a_1_0_filter_1(sK2))
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2))
    | sK1(X0,sK2) != sK4
    | sK0(X0,sK2) != sK3
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_413])).

cnf(c_673,plain,
    ( ~ r2_hidden(X0,a_1_0_filter_1(sK2))
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2))
    | sK1(X0,sK2) != sK4
    | sK0(X0,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_569])).

cnf(c_1069,plain,
    ( sK1(X0,sK2) != sK4
    | sK0(X0,sK2) != sK3
    | r2_hidden(X0,a_1_0_filter_1(sK2)) != iProver_top
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_1171,plain,
    ( sK1(X0,sK2) != sK4
    | sK0(X0,sK2) != sK3
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top
    | r2_hidden(k1_domain_1(u1_struct_0(sK2),u1_struct_0(sK2),sK3,sK4),k8_filter_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1069,c_453])).

cnf(c_1176,plain,
    ( sK1(X0,sK2) != sK4
    | sK0(X0,sK2) != sK3
    | r2_hidden(X0,k8_filter_1(sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1171,c_1153])).

cnf(c_9742,plain,
    ( sK0(k4_tarski(sK3,sK4),sK2) != sK3
    | r2_hidden(k4_tarski(sK3,sK4),k8_filter_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8739,c_1176])).

cnf(c_17,plain,
    ( X0 = X1
    | k4_tarski(X1,X2) != k4_tarski(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8724,plain,
    ( k4_tarski(X0,X1) != k4_tarski(sK3,sK4)
    | sK0(k4_tarski(sK3,sK4),sK2) = X0 ),
    inference(superposition,[status(thm)],[c_8645,c_17])).

cnf(c_8870,plain,
    ( sK0(k4_tarski(sK3,sK4),sK2) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_8724])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9742,c_8870,c_2843])).


%------------------------------------------------------------------------------

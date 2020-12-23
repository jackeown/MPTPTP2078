%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:59 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 402 expanded)
%              Number of clauses        :   76 ( 118 expanded)
%              Number of leaves         :   17 ( 118 expanded)
%              Depth                    :   18
%              Number of atoms          :  435 (2283 expanded)
%              Number of equality atoms :  112 ( 402 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r1_orders_2(X0,X2,X1)
          & r1_orders_2(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK5 != X1
        & r1_orders_2(X0,sK5,X1)
        & r1_orders_2(X0,X1,sK5)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK4 != X2
            & r1_orders_2(X0,X2,sK4)
            & r1_orders_2(X0,sK4,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r1_orders_2(X0,X2,X1)
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(sK3,X2,X1)
              & r1_orders_2(sK3,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( sK4 != sK5
    & r1_orders_2(sK3,sK5,sK4)
    & r1_orders_2(sK3,sK4,sK5)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f35,f34,f33])).

fof(f54,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    r1_orders_2(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( X2 = X3
                | ~ r2_hidden(k4_tarski(X3,X2),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK1(X0,X1) != sK2(X0,X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ( sK1(X0,X1) != sK2(X0,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).

fof(f43,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    r1_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_13,plain,
    ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_254,plain,
    ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_255,plain,
    ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_40,plain,
    ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_257,plain,
    ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_23,c_22,c_40])).

cnf(c_1034,plain,
    ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_257])).

cnf(c_1453,plain,
    ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_18,negated_conjecture,
    ( r1_orders_2(sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_15,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_274,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_275,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK3))
    | sK3 != sK3
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_275])).

cnf(c_324,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_326,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_21,c_20])).

cnf(c_1033,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) ),
    inference(subtyping,[status(esa)],[c_326])).

cnf(c_1454,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_11,plain,
    ( ~ r4_relat_2(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X0)
    | ~ r2_hidden(k4_tarski(X3,X2),X0)
    | ~ v1_relat_1(X0)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1036,plain,
    ( ~ r4_relat_2(X0_47,X1_47)
    | ~ r2_hidden(X2_47,X1_47)
    | ~ r2_hidden(X3_47,X1_47)
    | ~ r2_hidden(k4_tarski(X2_47,X3_47),X0_47)
    | ~ r2_hidden(k4_tarski(X3_47,X2_47),X0_47)
    | ~ v1_relat_1(X0_47)
    | X2_47 = X3_47 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1452,plain,
    ( X0_47 = X1_47
    | r4_relat_2(X2_47,X3_47) != iProver_top
    | r2_hidden(X0_47,X3_47) != iProver_top
    | r2_hidden(X1_47,X3_47) != iProver_top
    | r2_hidden(k4_tarski(X0_47,X1_47),X2_47) != iProver_top
    | r2_hidden(k4_tarski(X1_47,X0_47),X2_47) != iProver_top
    | v1_relat_1(X2_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_2429,plain,
    ( sK5 = sK4
    | r4_relat_2(u1_orders_2(sK3),X0_47) != iProver_top
    | r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) != iProver_top
    | r2_hidden(sK5,X0_47) != iProver_top
    | r2_hidden(sK4,X0_47) != iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_1452])).

cnf(c_26,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_325,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_1046,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1063,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_17,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1035,negated_conjecture,
    ( sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1047,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1634,plain,
    ( sK5 != X0_47
    | sK4 != X0_47
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_1635,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_267,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_268,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_409,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | u1_orders_2(sK3) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_268])).

cnf(c_410,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(u1_orders_2(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_1026,plain,
    ( ~ v1_relat_1(X0_47)
    | v1_relat_1(u1_orders_2(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_410])).

cnf(c_1461,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(X0_47)
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_2122,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != iProver_top
    | v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1461])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1042,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2136,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_2137,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2136])).

cnf(c_19,negated_conjecture,
    ( r1_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK3))
    | sK3 != sK3
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_275])).

cnf(c_335,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_337,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_21,c_20])).

cnf(c_1032,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) ),
    inference(subtyping,[status(esa)],[c_337])).

cnf(c_1455,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1032])).

cnf(c_2430,plain,
    ( sK5 = sK4
    | r4_relat_2(u1_orders_2(sK3),X0_47) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) != iProver_top
    | r2_hidden(sK5,X0_47) != iProver_top
    | r2_hidden(sK4,X0_47) != iProver_top
    | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_1452])).

cnf(c_2494,plain,
    ( r2_hidden(sK4,X0_47) != iProver_top
    | r2_hidden(sK5,X0_47) != iProver_top
    | r4_relat_2(u1_orders_2(sK3),X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2429,c_26,c_27,c_325,c_1063,c_1035,c_1635,c_2122,c_2137,c_2430])).

cnf(c_2495,plain,
    ( r4_relat_2(u1_orders_2(sK3),X0_47) != iProver_top
    | r2_hidden(sK5,X0_47) != iProver_top
    | r2_hidden(sK4,X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2494])).

cnf(c_2503,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_2495])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1043,plain,
    ( ~ r2_hidden(X0_47,X1_47)
    | ~ v1_xboole_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1700,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3))
    | ~ v1_xboole_0(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_1701,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) != iProver_top
    | v1_xboole_0(u1_orders_2(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1700])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_454,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_orders_2(sK3) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X2)) ),
    inference(resolution_lifted,[status(thm)],[c_5,c_268])).

cnf(c_455,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_orders_2(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_1023,plain,
    ( ~ v1_xboole_0(X0_47)
    | v1_xboole_0(u1_orders_2(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_455])).

cnf(c_1625,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_orders_2(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_1626,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_orders_2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_1624,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_359,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_360,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_361,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_349,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_struct_0(sK3) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_350,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_351,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2503,c_1701,c_1626,c_1624,c_361,c_351,c_325,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:49:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.18/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.18/1.00  
% 1.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.18/1.00  
% 1.18/1.00  ------  iProver source info
% 1.18/1.00  
% 1.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.18/1.00  git: non_committed_changes: false
% 1.18/1.00  git: last_make_outside_of_git: false
% 1.18/1.00  
% 1.18/1.00  ------ 
% 1.18/1.00  
% 1.18/1.00  ------ Input Options
% 1.18/1.00  
% 1.18/1.00  --out_options                           all
% 1.18/1.00  --tptp_safe_out                         true
% 1.18/1.00  --problem_path                          ""
% 1.18/1.00  --include_path                          ""
% 1.18/1.00  --clausifier                            res/vclausify_rel
% 1.18/1.00  --clausifier_options                    --mode clausify
% 1.18/1.00  --stdin                                 false
% 1.18/1.00  --stats_out                             all
% 1.18/1.00  
% 1.18/1.00  ------ General Options
% 1.18/1.00  
% 1.18/1.00  --fof                                   false
% 1.18/1.00  --time_out_real                         305.
% 1.18/1.00  --time_out_virtual                      -1.
% 1.18/1.00  --symbol_type_check                     false
% 1.18/1.00  --clausify_out                          false
% 1.18/1.00  --sig_cnt_out                           false
% 1.18/1.00  --trig_cnt_out                          false
% 1.18/1.00  --trig_cnt_out_tolerance                1.
% 1.18/1.00  --trig_cnt_out_sk_spl                   false
% 1.18/1.00  --abstr_cl_out                          false
% 1.18/1.00  
% 1.18/1.00  ------ Global Options
% 1.18/1.00  
% 1.18/1.00  --schedule                              default
% 1.18/1.00  --add_important_lit                     false
% 1.18/1.00  --prop_solver_per_cl                    1000
% 1.18/1.00  --min_unsat_core                        false
% 1.18/1.00  --soft_assumptions                      false
% 1.18/1.00  --soft_lemma_size                       3
% 1.18/1.00  --prop_impl_unit_size                   0
% 1.18/1.00  --prop_impl_unit                        []
% 1.18/1.00  --share_sel_clauses                     true
% 1.18/1.00  --reset_solvers                         false
% 1.18/1.00  --bc_imp_inh                            [conj_cone]
% 1.18/1.00  --conj_cone_tolerance                   3.
% 1.18/1.00  --extra_neg_conj                        none
% 1.18/1.00  --large_theory_mode                     true
% 1.18/1.00  --prolific_symb_bound                   200
% 1.18/1.00  --lt_threshold                          2000
% 1.18/1.00  --clause_weak_htbl                      true
% 1.18/1.00  --gc_record_bc_elim                     false
% 1.18/1.00  
% 1.18/1.00  ------ Preprocessing Options
% 1.18/1.00  
% 1.18/1.00  --preprocessing_flag                    true
% 1.18/1.00  --time_out_prep_mult                    0.1
% 1.18/1.00  --splitting_mode                        input
% 1.18/1.00  --splitting_grd                         true
% 1.18/1.00  --splitting_cvd                         false
% 1.18/1.00  --splitting_cvd_svl                     false
% 1.18/1.00  --splitting_nvd                         32
% 1.18/1.00  --sub_typing                            true
% 1.18/1.00  --prep_gs_sim                           true
% 1.18/1.00  --prep_unflatten                        true
% 1.18/1.00  --prep_res_sim                          true
% 1.18/1.00  --prep_upred                            true
% 1.18/1.00  --prep_sem_filter                       exhaustive
% 1.18/1.00  --prep_sem_filter_out                   false
% 1.18/1.00  --pred_elim                             true
% 1.18/1.00  --res_sim_input                         true
% 1.18/1.00  --eq_ax_congr_red                       true
% 1.18/1.00  --pure_diseq_elim                       true
% 1.18/1.00  --brand_transform                       false
% 1.18/1.00  --non_eq_to_eq                          false
% 1.18/1.00  --prep_def_merge                        true
% 1.18/1.00  --prep_def_merge_prop_impl              false
% 1.18/1.00  --prep_def_merge_mbd                    true
% 1.18/1.00  --prep_def_merge_tr_red                 false
% 1.18/1.00  --prep_def_merge_tr_cl                  false
% 1.18/1.00  --smt_preprocessing                     true
% 1.18/1.00  --smt_ac_axioms                         fast
% 1.18/1.00  --preprocessed_out                      false
% 1.18/1.00  --preprocessed_stats                    false
% 1.18/1.00  
% 1.18/1.00  ------ Abstraction refinement Options
% 1.18/1.00  
% 1.18/1.00  --abstr_ref                             []
% 1.18/1.00  --abstr_ref_prep                        false
% 1.18/1.00  --abstr_ref_until_sat                   false
% 1.18/1.00  --abstr_ref_sig_restrict                funpre
% 1.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/1.00  --abstr_ref_under                       []
% 1.18/1.00  
% 1.18/1.00  ------ SAT Options
% 1.18/1.00  
% 1.18/1.00  --sat_mode                              false
% 1.18/1.00  --sat_fm_restart_options                ""
% 1.18/1.00  --sat_gr_def                            false
% 1.18/1.00  --sat_epr_types                         true
% 1.18/1.00  --sat_non_cyclic_types                  false
% 1.18/1.00  --sat_finite_models                     false
% 1.18/1.00  --sat_fm_lemmas                         false
% 1.18/1.00  --sat_fm_prep                           false
% 1.18/1.00  --sat_fm_uc_incr                        true
% 1.18/1.00  --sat_out_model                         small
% 1.18/1.00  --sat_out_clauses                       false
% 1.18/1.00  
% 1.18/1.00  ------ QBF Options
% 1.18/1.00  
% 1.18/1.00  --qbf_mode                              false
% 1.18/1.00  --qbf_elim_univ                         false
% 1.18/1.00  --qbf_dom_inst                          none
% 1.18/1.00  --qbf_dom_pre_inst                      false
% 1.18/1.00  --qbf_sk_in                             false
% 1.18/1.00  --qbf_pred_elim                         true
% 1.18/1.00  --qbf_split                             512
% 1.18/1.00  
% 1.18/1.00  ------ BMC1 Options
% 1.18/1.00  
% 1.18/1.00  --bmc1_incremental                      false
% 1.18/1.00  --bmc1_axioms                           reachable_all
% 1.18/1.00  --bmc1_min_bound                        0
% 1.18/1.00  --bmc1_max_bound                        -1
% 1.18/1.00  --bmc1_max_bound_default                -1
% 1.18/1.00  --bmc1_symbol_reachability              true
% 1.18/1.00  --bmc1_property_lemmas                  false
% 1.18/1.00  --bmc1_k_induction                      false
% 1.18/1.00  --bmc1_non_equiv_states                 false
% 1.18/1.00  --bmc1_deadlock                         false
% 1.18/1.00  --bmc1_ucm                              false
% 1.18/1.00  --bmc1_add_unsat_core                   none
% 1.18/1.00  --bmc1_unsat_core_children              false
% 1.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/1.00  --bmc1_out_stat                         full
% 1.18/1.00  --bmc1_ground_init                      false
% 1.18/1.00  --bmc1_pre_inst_next_state              false
% 1.18/1.00  --bmc1_pre_inst_state                   false
% 1.18/1.00  --bmc1_pre_inst_reach_state             false
% 1.18/1.00  --bmc1_out_unsat_core                   false
% 1.18/1.00  --bmc1_aig_witness_out                  false
% 1.18/1.00  --bmc1_verbose                          false
% 1.18/1.00  --bmc1_dump_clauses_tptp                false
% 1.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.18/1.00  --bmc1_dump_file                        -
% 1.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.18/1.00  --bmc1_ucm_extend_mode                  1
% 1.18/1.00  --bmc1_ucm_init_mode                    2
% 1.18/1.00  --bmc1_ucm_cone_mode                    none
% 1.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.18/1.00  --bmc1_ucm_relax_model                  4
% 1.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/1.00  --bmc1_ucm_layered_model                none
% 1.18/1.00  --bmc1_ucm_max_lemma_size               10
% 1.18/1.00  
% 1.18/1.00  ------ AIG Options
% 1.18/1.00  
% 1.18/1.00  --aig_mode                              false
% 1.18/1.00  
% 1.18/1.00  ------ Instantiation Options
% 1.18/1.00  
% 1.18/1.00  --instantiation_flag                    true
% 1.18/1.00  --inst_sos_flag                         false
% 1.18/1.00  --inst_sos_phase                        true
% 1.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/1.00  --inst_lit_sel_side                     num_symb
% 1.18/1.00  --inst_solver_per_active                1400
% 1.18/1.00  --inst_solver_calls_frac                1.
% 1.18/1.00  --inst_passive_queue_type               priority_queues
% 1.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/1.00  --inst_passive_queues_freq              [25;2]
% 1.18/1.00  --inst_dismatching                      true
% 1.18/1.00  --inst_eager_unprocessed_to_passive     true
% 1.18/1.00  --inst_prop_sim_given                   true
% 1.18/1.00  --inst_prop_sim_new                     false
% 1.18/1.00  --inst_subs_new                         false
% 1.18/1.00  --inst_eq_res_simp                      false
% 1.18/1.00  --inst_subs_given                       false
% 1.18/1.00  --inst_orphan_elimination               true
% 1.18/1.00  --inst_learning_loop_flag               true
% 1.18/1.00  --inst_learning_start                   3000
% 1.18/1.00  --inst_learning_factor                  2
% 1.18/1.00  --inst_start_prop_sim_after_learn       3
% 1.18/1.00  --inst_sel_renew                        solver
% 1.18/1.00  --inst_lit_activity_flag                true
% 1.18/1.00  --inst_restr_to_given                   false
% 1.18/1.00  --inst_activity_threshold               500
% 1.18/1.00  --inst_out_proof                        true
% 1.18/1.00  
% 1.18/1.00  ------ Resolution Options
% 1.18/1.00  
% 1.18/1.00  --resolution_flag                       true
% 1.18/1.00  --res_lit_sel                           adaptive
% 1.18/1.00  --res_lit_sel_side                      none
% 1.18/1.00  --res_ordering                          kbo
% 1.18/1.00  --res_to_prop_solver                    active
% 1.18/1.00  --res_prop_simpl_new                    false
% 1.18/1.00  --res_prop_simpl_given                  true
% 1.18/1.00  --res_passive_queue_type                priority_queues
% 1.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/1.00  --res_passive_queues_freq               [15;5]
% 1.18/1.00  --res_forward_subs                      full
% 1.18/1.00  --res_backward_subs                     full
% 1.18/1.00  --res_forward_subs_resolution           true
% 1.18/1.00  --res_backward_subs_resolution          true
% 1.18/1.00  --res_orphan_elimination                true
% 1.18/1.00  --res_time_limit                        2.
% 1.18/1.00  --res_out_proof                         true
% 1.18/1.00  
% 1.18/1.00  ------ Superposition Options
% 1.18/1.00  
% 1.18/1.00  --superposition_flag                    true
% 1.18/1.00  --sup_passive_queue_type                priority_queues
% 1.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.18/1.00  --demod_completeness_check              fast
% 1.18/1.00  --demod_use_ground                      true
% 1.18/1.00  --sup_to_prop_solver                    passive
% 1.18/1.00  --sup_prop_simpl_new                    true
% 1.18/1.00  --sup_prop_simpl_given                  true
% 1.18/1.00  --sup_fun_splitting                     false
% 1.18/1.00  --sup_smt_interval                      50000
% 1.18/1.00  
% 1.18/1.00  ------ Superposition Simplification Setup
% 1.18/1.00  
% 1.18/1.00  --sup_indices_passive                   []
% 1.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.00  --sup_full_bw                           [BwDemod]
% 1.18/1.00  --sup_immed_triv                        [TrivRules]
% 1.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.00  --sup_immed_bw_main                     []
% 1.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.00  
% 1.18/1.00  ------ Combination Options
% 1.18/1.00  
% 1.18/1.00  --comb_res_mult                         3
% 1.18/1.00  --comb_sup_mult                         2
% 1.18/1.00  --comb_inst_mult                        10
% 1.18/1.00  
% 1.18/1.00  ------ Debug Options
% 1.18/1.00  
% 1.18/1.00  --dbg_backtrace                         false
% 1.18/1.00  --dbg_dump_prop_clauses                 false
% 1.18/1.00  --dbg_dump_prop_clauses_file            -
% 1.18/1.00  --dbg_out_stat                          false
% 1.18/1.00  ------ Parsing...
% 1.18/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.18/1.00  
% 1.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.18/1.00  
% 1.18/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.18/1.00  
% 1.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.18/1.00  ------ Proving...
% 1.18/1.00  ------ Problem Properties 
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  clauses                                 22
% 1.18/1.00  conjectures                             1
% 1.18/1.00  EPR                                     2
% 1.18/1.00  Horn                                    14
% 1.18/1.00  unary                                   5
% 1.18/1.00  binary                                  5
% 1.18/1.00  lits                                    55
% 1.18/1.00  lits eq                                 9
% 1.18/1.00  fd_pure                                 0
% 1.18/1.00  fd_pseudo                               0
% 1.18/1.00  fd_cond                                 0
% 1.18/1.00  fd_pseudo_cond                          1
% 1.18/1.00  AC symbols                              0
% 1.18/1.00  
% 1.18/1.00  ------ Schedule dynamic 5 is on 
% 1.18/1.00  
% 1.18/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  ------ 
% 1.18/1.00  Current options:
% 1.18/1.00  ------ 
% 1.18/1.00  
% 1.18/1.00  ------ Input Options
% 1.18/1.00  
% 1.18/1.00  --out_options                           all
% 1.18/1.00  --tptp_safe_out                         true
% 1.18/1.00  --problem_path                          ""
% 1.18/1.00  --include_path                          ""
% 1.18/1.00  --clausifier                            res/vclausify_rel
% 1.18/1.00  --clausifier_options                    --mode clausify
% 1.18/1.00  --stdin                                 false
% 1.18/1.00  --stats_out                             all
% 1.18/1.00  
% 1.18/1.00  ------ General Options
% 1.18/1.00  
% 1.18/1.00  --fof                                   false
% 1.18/1.00  --time_out_real                         305.
% 1.18/1.00  --time_out_virtual                      -1.
% 1.18/1.00  --symbol_type_check                     false
% 1.18/1.00  --clausify_out                          false
% 1.18/1.00  --sig_cnt_out                           false
% 1.18/1.00  --trig_cnt_out                          false
% 1.18/1.00  --trig_cnt_out_tolerance                1.
% 1.18/1.00  --trig_cnt_out_sk_spl                   false
% 1.18/1.00  --abstr_cl_out                          false
% 1.18/1.00  
% 1.18/1.00  ------ Global Options
% 1.18/1.00  
% 1.18/1.00  --schedule                              default
% 1.18/1.00  --add_important_lit                     false
% 1.18/1.00  --prop_solver_per_cl                    1000
% 1.18/1.00  --min_unsat_core                        false
% 1.18/1.00  --soft_assumptions                      false
% 1.18/1.00  --soft_lemma_size                       3
% 1.18/1.00  --prop_impl_unit_size                   0
% 1.18/1.00  --prop_impl_unit                        []
% 1.18/1.00  --share_sel_clauses                     true
% 1.18/1.00  --reset_solvers                         false
% 1.18/1.00  --bc_imp_inh                            [conj_cone]
% 1.18/1.00  --conj_cone_tolerance                   3.
% 1.18/1.00  --extra_neg_conj                        none
% 1.18/1.00  --large_theory_mode                     true
% 1.18/1.00  --prolific_symb_bound                   200
% 1.18/1.00  --lt_threshold                          2000
% 1.18/1.00  --clause_weak_htbl                      true
% 1.18/1.00  --gc_record_bc_elim                     false
% 1.18/1.00  
% 1.18/1.00  ------ Preprocessing Options
% 1.18/1.00  
% 1.18/1.00  --preprocessing_flag                    true
% 1.18/1.00  --time_out_prep_mult                    0.1
% 1.18/1.00  --splitting_mode                        input
% 1.18/1.00  --splitting_grd                         true
% 1.18/1.00  --splitting_cvd                         false
% 1.18/1.00  --splitting_cvd_svl                     false
% 1.18/1.00  --splitting_nvd                         32
% 1.18/1.00  --sub_typing                            true
% 1.18/1.00  --prep_gs_sim                           true
% 1.18/1.00  --prep_unflatten                        true
% 1.18/1.00  --prep_res_sim                          true
% 1.18/1.00  --prep_upred                            true
% 1.18/1.00  --prep_sem_filter                       exhaustive
% 1.18/1.00  --prep_sem_filter_out                   false
% 1.18/1.00  --pred_elim                             true
% 1.18/1.00  --res_sim_input                         true
% 1.18/1.00  --eq_ax_congr_red                       true
% 1.18/1.00  --pure_diseq_elim                       true
% 1.18/1.00  --brand_transform                       false
% 1.18/1.00  --non_eq_to_eq                          false
% 1.18/1.00  --prep_def_merge                        true
% 1.18/1.00  --prep_def_merge_prop_impl              false
% 1.18/1.00  --prep_def_merge_mbd                    true
% 1.18/1.00  --prep_def_merge_tr_red                 false
% 1.18/1.00  --prep_def_merge_tr_cl                  false
% 1.18/1.00  --smt_preprocessing                     true
% 1.18/1.00  --smt_ac_axioms                         fast
% 1.18/1.00  --preprocessed_out                      false
% 1.18/1.00  --preprocessed_stats                    false
% 1.18/1.00  
% 1.18/1.00  ------ Abstraction refinement Options
% 1.18/1.00  
% 1.18/1.00  --abstr_ref                             []
% 1.18/1.00  --abstr_ref_prep                        false
% 1.18/1.00  --abstr_ref_until_sat                   false
% 1.18/1.00  --abstr_ref_sig_restrict                funpre
% 1.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/1.00  --abstr_ref_under                       []
% 1.18/1.00  
% 1.18/1.00  ------ SAT Options
% 1.18/1.00  
% 1.18/1.00  --sat_mode                              false
% 1.18/1.00  --sat_fm_restart_options                ""
% 1.18/1.00  --sat_gr_def                            false
% 1.18/1.00  --sat_epr_types                         true
% 1.18/1.00  --sat_non_cyclic_types                  false
% 1.18/1.00  --sat_finite_models                     false
% 1.18/1.00  --sat_fm_lemmas                         false
% 1.18/1.00  --sat_fm_prep                           false
% 1.18/1.00  --sat_fm_uc_incr                        true
% 1.18/1.00  --sat_out_model                         small
% 1.18/1.00  --sat_out_clauses                       false
% 1.18/1.00  
% 1.18/1.00  ------ QBF Options
% 1.18/1.00  
% 1.18/1.00  --qbf_mode                              false
% 1.18/1.00  --qbf_elim_univ                         false
% 1.18/1.00  --qbf_dom_inst                          none
% 1.18/1.00  --qbf_dom_pre_inst                      false
% 1.18/1.00  --qbf_sk_in                             false
% 1.18/1.00  --qbf_pred_elim                         true
% 1.18/1.00  --qbf_split                             512
% 1.18/1.00  
% 1.18/1.00  ------ BMC1 Options
% 1.18/1.00  
% 1.18/1.00  --bmc1_incremental                      false
% 1.18/1.00  --bmc1_axioms                           reachable_all
% 1.18/1.00  --bmc1_min_bound                        0
% 1.18/1.00  --bmc1_max_bound                        -1
% 1.18/1.00  --bmc1_max_bound_default                -1
% 1.18/1.00  --bmc1_symbol_reachability              true
% 1.18/1.00  --bmc1_property_lemmas                  false
% 1.18/1.00  --bmc1_k_induction                      false
% 1.18/1.00  --bmc1_non_equiv_states                 false
% 1.18/1.00  --bmc1_deadlock                         false
% 1.18/1.00  --bmc1_ucm                              false
% 1.18/1.00  --bmc1_add_unsat_core                   none
% 1.18/1.00  --bmc1_unsat_core_children              false
% 1.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/1.00  --bmc1_out_stat                         full
% 1.18/1.00  --bmc1_ground_init                      false
% 1.18/1.00  --bmc1_pre_inst_next_state              false
% 1.18/1.00  --bmc1_pre_inst_state                   false
% 1.18/1.00  --bmc1_pre_inst_reach_state             false
% 1.18/1.00  --bmc1_out_unsat_core                   false
% 1.18/1.00  --bmc1_aig_witness_out                  false
% 1.18/1.00  --bmc1_verbose                          false
% 1.18/1.00  --bmc1_dump_clauses_tptp                false
% 1.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.18/1.00  --bmc1_dump_file                        -
% 1.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.18/1.00  --bmc1_ucm_extend_mode                  1
% 1.18/1.00  --bmc1_ucm_init_mode                    2
% 1.18/1.00  --bmc1_ucm_cone_mode                    none
% 1.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.18/1.00  --bmc1_ucm_relax_model                  4
% 1.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/1.00  --bmc1_ucm_layered_model                none
% 1.18/1.00  --bmc1_ucm_max_lemma_size               10
% 1.18/1.00  
% 1.18/1.00  ------ AIG Options
% 1.18/1.00  
% 1.18/1.00  --aig_mode                              false
% 1.18/1.00  
% 1.18/1.00  ------ Instantiation Options
% 1.18/1.00  
% 1.18/1.00  --instantiation_flag                    true
% 1.18/1.00  --inst_sos_flag                         false
% 1.18/1.00  --inst_sos_phase                        true
% 1.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/1.00  --inst_lit_sel_side                     none
% 1.18/1.00  --inst_solver_per_active                1400
% 1.18/1.00  --inst_solver_calls_frac                1.
% 1.18/1.00  --inst_passive_queue_type               priority_queues
% 1.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/1.00  --inst_passive_queues_freq              [25;2]
% 1.18/1.00  --inst_dismatching                      true
% 1.18/1.00  --inst_eager_unprocessed_to_passive     true
% 1.18/1.00  --inst_prop_sim_given                   true
% 1.18/1.00  --inst_prop_sim_new                     false
% 1.18/1.00  --inst_subs_new                         false
% 1.18/1.00  --inst_eq_res_simp                      false
% 1.18/1.00  --inst_subs_given                       false
% 1.18/1.00  --inst_orphan_elimination               true
% 1.18/1.00  --inst_learning_loop_flag               true
% 1.18/1.00  --inst_learning_start                   3000
% 1.18/1.00  --inst_learning_factor                  2
% 1.18/1.00  --inst_start_prop_sim_after_learn       3
% 1.18/1.00  --inst_sel_renew                        solver
% 1.18/1.00  --inst_lit_activity_flag                true
% 1.18/1.00  --inst_restr_to_given                   false
% 1.18/1.00  --inst_activity_threshold               500
% 1.18/1.00  --inst_out_proof                        true
% 1.18/1.00  
% 1.18/1.00  ------ Resolution Options
% 1.18/1.00  
% 1.18/1.00  --resolution_flag                       false
% 1.18/1.00  --res_lit_sel                           adaptive
% 1.18/1.00  --res_lit_sel_side                      none
% 1.18/1.00  --res_ordering                          kbo
% 1.18/1.00  --res_to_prop_solver                    active
% 1.18/1.00  --res_prop_simpl_new                    false
% 1.18/1.00  --res_prop_simpl_given                  true
% 1.18/1.00  --res_passive_queue_type                priority_queues
% 1.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/1.00  --res_passive_queues_freq               [15;5]
% 1.18/1.00  --res_forward_subs                      full
% 1.18/1.00  --res_backward_subs                     full
% 1.18/1.00  --res_forward_subs_resolution           true
% 1.18/1.00  --res_backward_subs_resolution          true
% 1.18/1.00  --res_orphan_elimination                true
% 1.18/1.00  --res_time_limit                        2.
% 1.18/1.00  --res_out_proof                         true
% 1.18/1.00  
% 1.18/1.00  ------ Superposition Options
% 1.18/1.00  
% 1.18/1.00  --superposition_flag                    true
% 1.18/1.00  --sup_passive_queue_type                priority_queues
% 1.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.18/1.00  --demod_completeness_check              fast
% 1.18/1.00  --demod_use_ground                      true
% 1.18/1.00  --sup_to_prop_solver                    passive
% 1.18/1.00  --sup_prop_simpl_new                    true
% 1.18/1.00  --sup_prop_simpl_given                  true
% 1.18/1.00  --sup_fun_splitting                     false
% 1.18/1.00  --sup_smt_interval                      50000
% 1.18/1.00  
% 1.18/1.00  ------ Superposition Simplification Setup
% 1.18/1.00  
% 1.18/1.00  --sup_indices_passive                   []
% 1.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.00  --sup_full_bw                           [BwDemod]
% 1.18/1.00  --sup_immed_triv                        [TrivRules]
% 1.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.00  --sup_immed_bw_main                     []
% 1.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.00  
% 1.18/1.00  ------ Combination Options
% 1.18/1.00  
% 1.18/1.00  --comb_res_mult                         3
% 1.18/1.00  --comb_sup_mult                         2
% 1.18/1.00  --comb_inst_mult                        10
% 1.18/1.00  
% 1.18/1.00  ------ Debug Options
% 1.18/1.00  
% 1.18/1.00  --dbg_backtrace                         false
% 1.18/1.00  --dbg_dump_prop_clauses                 false
% 1.18/1.00  --dbg_dump_prop_clauses_file            -
% 1.18/1.00  --dbg_out_stat                          false
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  ------ Proving...
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  % SZS status Theorem for theBenchmark.p
% 1.18/1.00  
% 1.18/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.18/1.00  
% 1.18/1.00  fof(f7,axiom,(
% 1.18/1.00    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f18,plain,(
% 1.18/1.00    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.18/1.00    inference(ennf_transformation,[],[f7])).
% 1.18/1.00  
% 1.18/1.00  fof(f31,plain,(
% 1.18/1.00    ! [X0] : (((v5_orders_2(X0) | ~r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0))) | ~l1_orders_2(X0))),
% 1.18/1.00    inference(nnf_transformation,[],[f18])).
% 1.18/1.00  
% 1.18/1.00  fof(f49,plain,(
% 1.18/1.00    ( ! [X0] : (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~l1_orders_2(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f31])).
% 1.18/1.00  
% 1.18/1.00  fof(f10,conjecture,(
% 1.18/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f11,negated_conjecture,(
% 1.18/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 1.18/1.00    inference(negated_conjecture,[],[f10])).
% 1.18/1.00  
% 1.18/1.00  fof(f21,plain,(
% 1.18/1.00    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0)))),
% 1.18/1.00    inference(ennf_transformation,[],[f11])).
% 1.18/1.00  
% 1.18/1.00  fof(f22,plain,(
% 1.18/1.00    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0))),
% 1.18/1.00    inference(flattening,[],[f21])).
% 1.18/1.00  
% 1.18/1.00  fof(f35,plain,(
% 1.18/1.00    ( ! [X0,X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (sK5 != X1 & r1_orders_2(X0,sK5,X1) & r1_orders_2(X0,X1,sK5) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f34,plain,(
% 1.18/1.00    ( ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK4 != X2 & r1_orders_2(X0,X2,sK4) & r1_orders_2(X0,sK4,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f33,plain,(
% 1.18/1.00    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(sK3,X2,X1) & r1_orders_2(sK3,X1,X2) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f36,plain,(
% 1.18/1.00    ((sK4 != sK5 & r1_orders_2(sK3,sK5,sK4) & r1_orders_2(sK3,sK4,sK5) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3)),
% 1.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f35,f34,f33])).
% 1.18/1.00  
% 1.18/1.00  fof(f54,plain,(
% 1.18/1.00    v5_orders_2(sK3)),
% 1.18/1.00    inference(cnf_transformation,[],[f36])).
% 1.18/1.00  
% 1.18/1.00  fof(f55,plain,(
% 1.18/1.00    l1_orders_2(sK3)),
% 1.18/1.00    inference(cnf_transformation,[],[f36])).
% 1.18/1.00  
% 1.18/1.00  fof(f59,plain,(
% 1.18/1.00    r1_orders_2(sK3,sK5,sK4)),
% 1.18/1.00    inference(cnf_transformation,[],[f36])).
% 1.18/1.00  
% 1.18/1.00  fof(f8,axiom,(
% 1.18/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f19,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.18/1.00    inference(ennf_transformation,[],[f8])).
% 1.18/1.00  
% 1.18/1.00  fof(f32,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.18/1.00    inference(nnf_transformation,[],[f19])).
% 1.18/1.00  
% 1.18/1.00  fof(f51,plain,(
% 1.18/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f32])).
% 1.18/1.00  
% 1.18/1.00  fof(f56,plain,(
% 1.18/1.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.18/1.00    inference(cnf_transformation,[],[f36])).
% 1.18/1.00  
% 1.18/1.00  fof(f57,plain,(
% 1.18/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.18/1.00    inference(cnf_transformation,[],[f36])).
% 1.18/1.00  
% 1.18/1.00  fof(f6,axiom,(
% 1.18/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : ((r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => X2 = X3)))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f16,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 1.18/1.00    inference(ennf_transformation,[],[f6])).
% 1.18/1.00  
% 1.18/1.00  fof(f17,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 1.18/1.00    inference(flattening,[],[f16])).
% 1.18/1.00  
% 1.18/1.00  fof(f27,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r4_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.18/1.00    inference(nnf_transformation,[],[f17])).
% 1.18/1.00  
% 1.18/1.00  fof(f28,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~r4_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.18/1.00    inference(rectify,[],[f27])).
% 1.18/1.00  
% 1.18/1.00  fof(f29,plain,(
% 1.18/1.00    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK1(X0,X1) != sK2(X0,X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1)))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f30,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | (sK1(X0,X1) != sK2(X0,X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~r4_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).
% 1.18/1.00  
% 1.18/1.00  fof(f43,plain,(
% 1.18/1.00    ( ! [X4,X0,X5,X1] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f30])).
% 1.18/1.00  
% 1.18/1.00  fof(f60,plain,(
% 1.18/1.00    sK4 != sK5),
% 1.18/1.00    inference(cnf_transformation,[],[f36])).
% 1.18/1.00  
% 1.18/1.00  fof(f3,axiom,(
% 1.18/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f14,plain,(
% 1.18/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.18/1.00    inference(ennf_transformation,[],[f3])).
% 1.18/1.00  
% 1.18/1.00  fof(f40,plain,(
% 1.18/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f14])).
% 1.18/1.00  
% 1.18/1.00  fof(f9,axiom,(
% 1.18/1.00    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f20,plain,(
% 1.18/1.00    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.18/1.00    inference(ennf_transformation,[],[f9])).
% 1.18/1.00  
% 1.18/1.00  fof(f53,plain,(
% 1.18/1.00    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f20])).
% 1.18/1.00  
% 1.18/1.00  fof(f4,axiom,(
% 1.18/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f41,plain,(
% 1.18/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.18/1.00    inference(cnf_transformation,[],[f4])).
% 1.18/1.00  
% 1.18/1.00  fof(f58,plain,(
% 1.18/1.00    r1_orders_2(sK3,sK4,sK5)),
% 1.18/1.00    inference(cnf_transformation,[],[f36])).
% 1.18/1.00  
% 1.18/1.00  fof(f1,axiom,(
% 1.18/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f23,plain,(
% 1.18/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.18/1.00    inference(nnf_transformation,[],[f1])).
% 1.18/1.00  
% 1.18/1.00  fof(f24,plain,(
% 1.18/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.18/1.00    inference(rectify,[],[f23])).
% 1.18/1.00  
% 1.18/1.00  fof(f25,plain,(
% 1.18/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f26,plain,(
% 1.18/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 1.18/1.00  
% 1.18/1.00  fof(f37,plain,(
% 1.18/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f26])).
% 1.18/1.00  
% 1.18/1.00  fof(f5,axiom,(
% 1.18/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f15,plain,(
% 1.18/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.18/1.00    inference(ennf_transformation,[],[f5])).
% 1.18/1.00  
% 1.18/1.00  fof(f42,plain,(
% 1.18/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f15])).
% 1.18/1.00  
% 1.18/1.00  fof(f2,axiom,(
% 1.18/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f12,plain,(
% 1.18/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.18/1.00    inference(ennf_transformation,[],[f2])).
% 1.18/1.00  
% 1.18/1.00  fof(f13,plain,(
% 1.18/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.18/1.00    inference(flattening,[],[f12])).
% 1.18/1.00  
% 1.18/1.00  fof(f39,plain,(
% 1.18/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f13])).
% 1.18/1.00  
% 1.18/1.00  cnf(c_13,plain,
% 1.18/1.00      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
% 1.18/1.00      | ~ l1_orders_2(X0)
% 1.18/1.00      | ~ v5_orders_2(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_23,negated_conjecture,
% 1.18/1.00      ( v5_orders_2(sK3) ),
% 1.18/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_254,plain,
% 1.18/1.00      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
% 1.18/1.00      | ~ l1_orders_2(X0)
% 1.18/1.00      | sK3 != X0 ),
% 1.18/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_255,plain,
% 1.18/1.00      ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
% 1.18/1.00      | ~ l1_orders_2(sK3) ),
% 1.18/1.00      inference(unflattening,[status(thm)],[c_254]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_22,negated_conjecture,
% 1.18/1.00      ( l1_orders_2(sK3) ),
% 1.18/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_40,plain,
% 1.18/1.00      ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
% 1.18/1.00      | ~ l1_orders_2(sK3)
% 1.18/1.00      | ~ v5_orders_2(sK3) ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_257,plain,
% 1.18/1.00      ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_255,c_23,c_22,c_40]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1034,plain,
% 1.18/1.00      ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_257]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1453,plain,
% 1.18/1.00      ( r4_relat_2(u1_orders_2(sK3),u1_struct_0(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_18,negated_conjecture,
% 1.18/1.00      ( r1_orders_2(sK3,sK5,sK4) ),
% 1.18/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_15,plain,
% 1.18/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.18/1.00      | ~ l1_orders_2(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_274,plain,
% 1.18/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.18/1.00      | sK3 != X0 ),
% 1.18/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_275,plain,
% 1.18/1.00      ( ~ r1_orders_2(sK3,X0,X1)
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.18/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.18/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
% 1.18/1.00      inference(unflattening,[status(thm)],[c_274]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_323,plain,
% 1.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.18/1.00      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK3))
% 1.18/1.00      | sK3 != sK3
% 1.18/1.00      | sK5 != X1
% 1.18/1.00      | sK4 != X0 ),
% 1.18/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_275]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_324,plain,
% 1.18/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.18/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.18/1.00      | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) ),
% 1.18/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_21,negated_conjecture,
% 1.18/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.18/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_20,negated_conjecture,
% 1.18/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.18/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_326,plain,
% 1.18/1.00      ( r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_324,c_21,c_20]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1033,plain,
% 1.18/1.00      ( r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_326]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1454,plain,
% 1.18/1.00      ( r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_11,plain,
% 1.18/1.00      ( ~ r4_relat_2(X0,X1)
% 1.18/1.00      | ~ r2_hidden(X2,X1)
% 1.18/1.00      | ~ r2_hidden(X3,X1)
% 1.18/1.00      | ~ r2_hidden(k4_tarski(X2,X3),X0)
% 1.18/1.00      | ~ r2_hidden(k4_tarski(X3,X2),X0)
% 1.18/1.00      | ~ v1_relat_1(X0)
% 1.18/1.00      | X2 = X3 ),
% 1.18/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1036,plain,
% 1.18/1.00      ( ~ r4_relat_2(X0_47,X1_47)
% 1.18/1.00      | ~ r2_hidden(X2_47,X1_47)
% 1.18/1.00      | ~ r2_hidden(X3_47,X1_47)
% 1.18/1.00      | ~ r2_hidden(k4_tarski(X2_47,X3_47),X0_47)
% 1.18/1.00      | ~ r2_hidden(k4_tarski(X3_47,X2_47),X0_47)
% 1.18/1.00      | ~ v1_relat_1(X0_47)
% 1.18/1.00      | X2_47 = X3_47 ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1452,plain,
% 1.18/1.00      ( X0_47 = X1_47
% 1.18/1.00      | r4_relat_2(X2_47,X3_47) != iProver_top
% 1.18/1.00      | r2_hidden(X0_47,X3_47) != iProver_top
% 1.18/1.00      | r2_hidden(X1_47,X3_47) != iProver_top
% 1.18/1.00      | r2_hidden(k4_tarski(X0_47,X1_47),X2_47) != iProver_top
% 1.18/1.00      | r2_hidden(k4_tarski(X1_47,X0_47),X2_47) != iProver_top
% 1.18/1.00      | v1_relat_1(X2_47) != iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2429,plain,
% 1.18/1.00      ( sK5 = sK4
% 1.18/1.00      | r4_relat_2(u1_orders_2(sK3),X0_47) != iProver_top
% 1.18/1.00      | r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) != iProver_top
% 1.18/1.00      | r2_hidden(sK5,X0_47) != iProver_top
% 1.18/1.00      | r2_hidden(sK4,X0_47) != iProver_top
% 1.18/1.00      | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_1454,c_1452]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_26,plain,
% 1.18/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_27,plain,
% 1.18/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_325,plain,
% 1.18/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.18/1.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 1.18/1.00      | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1046,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1063,plain,
% 1.18/1.00      ( sK4 = sK4 ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_1046]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_17,negated_conjecture,
% 1.18/1.00      ( sK4 != sK5 ),
% 1.18/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1035,negated_conjecture,
% 1.18/1.00      ( sK4 != sK5 ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1047,plain,
% 1.18/1.00      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 1.18/1.00      theory(equality) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1634,plain,
% 1.18/1.00      ( sK5 != X0_47 | sK4 != X0_47 | sK4 = sK5 ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_1047]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1635,plain,
% 1.18/1.00      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_1634]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_3,plain,
% 1.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.18/1.00      | ~ v1_relat_1(X1)
% 1.18/1.00      | v1_relat_1(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_16,plain,
% 1.18/1.00      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.18/1.00      | ~ l1_orders_2(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_267,plain,
% 1.18/1.00      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.18/1.00      | sK3 != X0 ),
% 1.18/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_268,plain,
% 1.18/1.00      ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
% 1.18/1.00      inference(unflattening,[status(thm)],[c_267]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_409,plain,
% 1.18/1.00      ( ~ v1_relat_1(X0)
% 1.18/1.00      | v1_relat_1(X1)
% 1.18/1.00      | u1_orders_2(sK3) != X1
% 1.18/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(X0) ),
% 1.18/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_268]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_410,plain,
% 1.18/1.00      ( ~ v1_relat_1(X0)
% 1.18/1.00      | v1_relat_1(u1_orders_2(sK3))
% 1.18/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(X0) ),
% 1.18/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1026,plain,
% 1.18/1.00      ( ~ v1_relat_1(X0_47)
% 1.18/1.00      | v1_relat_1(u1_orders_2(sK3))
% 1.18/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(X0_47) ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_410]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1461,plain,
% 1.18/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(X0_47)
% 1.18/1.00      | v1_relat_1(X0_47) != iProver_top
% 1.18/1.00      | v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1026]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2122,plain,
% 1.18/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != iProver_top
% 1.18/1.00      | v1_relat_1(u1_orders_2(sK3)) = iProver_top ),
% 1.18/1.00      inference(equality_resolution,[status(thm)],[c_1461]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_4,plain,
% 1.18/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.18/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1042,plain,
% 1.18/1.00      ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2136,plain,
% 1.18/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_1042]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2137,plain,
% 1.18/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2136]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_19,negated_conjecture,
% 1.18/1.00      ( r1_orders_2(sK3,sK4,sK5) ),
% 1.18/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_334,plain,
% 1.18/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.18/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.18/1.00      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK3))
% 1.18/1.00      | sK3 != sK3
% 1.18/1.00      | sK5 != X0
% 1.18/1.00      | sK4 != X1 ),
% 1.18/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_275]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_335,plain,
% 1.18/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.18/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.18/1.00      | r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) ),
% 1.18/1.00      inference(unflattening,[status(thm)],[c_334]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_337,plain,
% 1.18/1.00      ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_335,c_21,c_20]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1032,plain,
% 1.18/1.00      ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_337]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1455,plain,
% 1.18/1.00      ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1032]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2430,plain,
% 1.18/1.00      ( sK5 = sK4
% 1.18/1.00      | r4_relat_2(u1_orders_2(sK3),X0_47) != iProver_top
% 1.18/1.00      | r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) != iProver_top
% 1.18/1.00      | r2_hidden(sK5,X0_47) != iProver_top
% 1.18/1.00      | r2_hidden(sK4,X0_47) != iProver_top
% 1.18/1.00      | v1_relat_1(u1_orders_2(sK3)) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_1455,c_1452]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2494,plain,
% 1.18/1.00      ( r2_hidden(sK4,X0_47) != iProver_top
% 1.18/1.00      | r2_hidden(sK5,X0_47) != iProver_top
% 1.18/1.00      | r4_relat_2(u1_orders_2(sK3),X0_47) != iProver_top ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_2429,c_26,c_27,c_325,c_1063,c_1035,c_1635,c_2122,
% 1.18/1.00                 c_2137,c_2430]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2495,plain,
% 1.18/1.00      ( r4_relat_2(u1_orders_2(sK3),X0_47) != iProver_top
% 1.18/1.00      | r2_hidden(sK5,X0_47) != iProver_top
% 1.18/1.00      | r2_hidden(sK4,X0_47) != iProver_top ),
% 1.18/1.00      inference(renaming,[status(thm)],[c_2494]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2503,plain,
% 1.18/1.00      ( r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
% 1.18/1.00      | r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_1453,c_2495]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1,plain,
% 1.18/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.18/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1043,plain,
% 1.18/1.00      ( ~ r2_hidden(X0_47,X1_47) | ~ v1_xboole_0(X1_47) ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1700,plain,
% 1.18/1.00      ( ~ r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3))
% 1.18/1.00      | ~ v1_xboole_0(u1_orders_2(sK3)) ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_1043]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1701,plain,
% 1.18/1.00      ( r2_hidden(k4_tarski(sK5,sK4),u1_orders_2(sK3)) != iProver_top
% 1.18/1.00      | v1_xboole_0(u1_orders_2(sK3)) != iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1700]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_5,plain,
% 1.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.18/1.00      | ~ v1_xboole_0(X1)
% 1.18/1.00      | v1_xboole_0(X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_454,plain,
% 1.18/1.00      ( ~ v1_xboole_0(X0)
% 1.18/1.00      | v1_xboole_0(X1)
% 1.18/1.00      | u1_orders_2(sK3) != X1
% 1.18/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X2)) ),
% 1.18/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_268]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_455,plain,
% 1.18/1.00      ( ~ v1_xboole_0(X0)
% 1.18/1.00      | v1_xboole_0(u1_orders_2(sK3))
% 1.18/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.18/1.00      inference(unflattening,[status(thm)],[c_454]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1023,plain,
% 1.18/1.00      ( ~ v1_xboole_0(X0_47)
% 1.18/1.00      | v1_xboole_0(u1_orders_2(sK3))
% 1.18/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 1.18/1.00      inference(subtyping,[status(esa)],[c_455]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1625,plain,
% 1.18/1.00      ( ~ v1_xboole_0(u1_struct_0(sK3))
% 1.18/1.00      | v1_xboole_0(u1_orders_2(sK3))
% 1.18/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_1023]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1626,plain,
% 1.18/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
% 1.18/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 1.18/1.00      | v1_xboole_0(u1_orders_2(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1625]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1624,plain,
% 1.18/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_1046]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2,plain,
% 1.18/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.18/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_359,plain,
% 1.18/1.00      ( r2_hidden(X0,X1)
% 1.18/1.00      | v1_xboole_0(X1)
% 1.18/1.00      | u1_struct_0(sK3) != X1
% 1.18/1.00      | sK4 != X0 ),
% 1.18/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_360,plain,
% 1.18/1.00      ( r2_hidden(sK4,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.18/1.00      inference(unflattening,[status(thm)],[c_359]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_361,plain,
% 1.18/1.00      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 1.18/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_349,plain,
% 1.18/1.00      ( r2_hidden(X0,X1)
% 1.18/1.00      | v1_xboole_0(X1)
% 1.18/1.00      | u1_struct_0(sK3) != X1
% 1.18/1.00      | sK5 != X0 ),
% 1.18/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_350,plain,
% 1.18/1.00      ( r2_hidden(sK5,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.18/1.00      inference(unflattening,[status(thm)],[c_349]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_351,plain,
% 1.18/1.00      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 1.18/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(contradiction,plain,
% 1.18/1.00      ( $false ),
% 1.18/1.00      inference(minisat,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_2503,c_1701,c_1626,c_1624,c_361,c_351,c_325,c_27,c_26]) ).
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.18/1.00  
% 1.18/1.00  ------                               Statistics
% 1.18/1.00  
% 1.18/1.00  ------ General
% 1.18/1.00  
% 1.18/1.00  abstr_ref_over_cycles:                  0
% 1.18/1.00  abstr_ref_under_cycles:                 0
% 1.18/1.00  gc_basic_clause_elim:                   0
% 1.18/1.00  forced_gc_time:                         0
% 1.18/1.00  parsing_time:                           0.01
% 1.18/1.00  unif_index_cands_time:                  0.
% 1.18/1.00  unif_index_add_time:                    0.
% 1.18/1.00  orderings_time:                         0.
% 1.18/1.00  out_proof_time:                         0.01
% 1.18/1.00  total_time:                             0.12
% 1.18/1.00  num_of_symbols:                         52
% 1.18/1.00  num_of_terms:                           2362
% 1.18/1.00  
% 1.18/1.00  ------ Preprocessing
% 1.18/1.00  
% 1.18/1.00  num_of_splits:                          0
% 1.18/1.00  num_of_split_atoms:                     0
% 1.18/1.00  num_of_reused_defs:                     0
% 1.18/1.00  num_eq_ax_congr_red:                    19
% 1.18/1.00  num_of_sem_filtered_clauses:            1
% 1.18/1.00  num_of_subtypes:                        2
% 1.18/1.00  monotx_restored_types:                  0
% 1.18/1.00  sat_num_of_epr_types:                   0
% 1.18/1.00  sat_num_of_non_cyclic_types:            0
% 1.18/1.00  sat_guarded_non_collapsed_types:        1
% 1.18/1.00  num_pure_diseq_elim:                    0
% 1.18/1.00  simp_replaced_by:                       0
% 1.18/1.00  res_preprocessed:                       109
% 1.18/1.00  prep_upred:                             0
% 1.18/1.00  prep_unflattend:                        24
% 1.18/1.00  smt_new_axioms:                         0
% 1.18/1.00  pred_elim_cands:                        4
% 1.18/1.00  pred_elim:                              4
% 1.18/1.00  pred_elim_cl:                           2
% 1.18/1.00  pred_elim_cycles:                       6
% 1.18/1.00  merged_defs:                            0
% 1.18/1.00  merged_defs_ncl:                        0
% 1.18/1.00  bin_hyper_res:                          0
% 1.18/1.00  prep_cycles:                            4
% 1.18/1.00  pred_elim_time:                         0.011
% 1.18/1.00  splitting_time:                         0.
% 1.18/1.00  sem_filter_time:                        0.
% 1.18/1.00  monotx_time:                            0.
% 1.18/1.00  subtype_inf_time:                       0.
% 1.18/1.00  
% 1.18/1.00  ------ Problem properties
% 1.18/1.00  
% 1.18/1.00  clauses:                                22
% 1.18/1.00  conjectures:                            1
% 1.18/1.00  epr:                                    2
% 1.18/1.00  horn:                                   14
% 1.18/1.00  ground:                                 7
% 1.18/1.00  unary:                                  5
% 1.18/1.00  binary:                                 5
% 1.18/1.00  lits:                                   55
% 1.18/1.00  lits_eq:                                9
% 1.18/1.00  fd_pure:                                0
% 1.18/1.00  fd_pseudo:                              0
% 1.18/1.00  fd_cond:                                0
% 1.18/1.00  fd_pseudo_cond:                         1
% 1.18/1.00  ac_symbols:                             0
% 1.18/1.00  
% 1.18/1.00  ------ Propositional Solver
% 1.18/1.00  
% 1.18/1.00  prop_solver_calls:                      26
% 1.18/1.00  prop_fast_solver_calls:                 757
% 1.18/1.00  smt_solver_calls:                       0
% 1.18/1.00  smt_fast_solver_calls:                  0
% 1.18/1.00  prop_num_of_clauses:                    645
% 1.18/1.00  prop_preprocess_simplified:             3399
% 1.18/1.00  prop_fo_subsumed:                       12
% 1.18/1.00  prop_solver_time:                       0.
% 1.18/1.00  smt_solver_time:                        0.
% 1.18/1.00  smt_fast_solver_time:                   0.
% 1.18/1.00  prop_fast_solver_time:                  0.
% 1.18/1.00  prop_unsat_core_time:                   0.
% 1.18/1.00  
% 1.18/1.00  ------ QBF
% 1.18/1.00  
% 1.18/1.00  qbf_q_res:                              0
% 1.18/1.00  qbf_num_tautologies:                    0
% 1.18/1.00  qbf_prep_cycles:                        0
% 1.18/1.00  
% 1.18/1.00  ------ BMC1
% 1.18/1.00  
% 1.18/1.00  bmc1_current_bound:                     -1
% 1.18/1.00  bmc1_last_solved_bound:                 -1
% 1.18/1.00  bmc1_unsat_core_size:                   -1
% 1.18/1.00  bmc1_unsat_core_parents_size:           -1
% 1.18/1.00  bmc1_merge_next_fun:                    0
% 1.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.18/1.00  
% 1.18/1.00  ------ Instantiation
% 1.18/1.00  
% 1.18/1.00  inst_num_of_clauses:                    165
% 1.18/1.00  inst_num_in_passive:                    9
% 1.18/1.00  inst_num_in_active:                     123
% 1.18/1.00  inst_num_in_unprocessed:                33
% 1.18/1.00  inst_num_of_loops:                      130
% 1.18/1.00  inst_num_of_learning_restarts:          0
% 1.18/1.00  inst_num_moves_active_passive:          5
% 1.18/1.00  inst_lit_activity:                      0
% 1.18/1.00  inst_lit_activity_moves:                0
% 1.18/1.00  inst_num_tautologies:                   0
% 1.18/1.00  inst_num_prop_implied:                  0
% 1.18/1.00  inst_num_existing_simplified:           0
% 1.18/1.00  inst_num_eq_res_simplified:             0
% 1.18/1.00  inst_num_child_elim:                    0
% 1.18/1.00  inst_num_of_dismatching_blockings:      12
% 1.18/1.00  inst_num_of_non_proper_insts:           178
% 1.18/1.00  inst_num_of_duplicates:                 0
% 1.18/1.00  inst_inst_num_from_inst_to_res:         0
% 1.18/1.00  inst_dismatching_checking_time:         0.
% 1.18/1.00  
% 1.18/1.00  ------ Resolution
% 1.18/1.00  
% 1.18/1.00  res_num_of_clauses:                     0
% 1.18/1.00  res_num_in_passive:                     0
% 1.18/1.00  res_num_in_active:                      0
% 1.18/1.00  res_num_of_loops:                       113
% 1.18/1.00  res_forward_subset_subsumed:            18
% 1.18/1.00  res_backward_subset_subsumed:           0
% 1.18/1.00  res_forward_subsumed:                   0
% 1.18/1.00  res_backward_subsumed:                  0
% 1.18/1.00  res_forward_subsumption_resolution:     0
% 1.18/1.00  res_backward_subsumption_resolution:    0
% 1.18/1.00  res_clause_to_clause_subsumption:       47
% 1.18/1.00  res_orphan_elimination:                 0
% 1.18/1.00  res_tautology_del:                      21
% 1.18/1.00  res_num_eq_res_simplified:              0
% 1.18/1.00  res_num_sel_changes:                    0
% 1.18/1.00  res_moves_from_active_to_pass:          0
% 1.18/1.00  
% 1.18/1.00  ------ Superposition
% 1.18/1.00  
% 1.18/1.00  sup_time_total:                         0.
% 1.18/1.00  sup_time_generating:                    0.
% 1.18/1.00  sup_time_sim_full:                      0.
% 1.18/1.00  sup_time_sim_immed:                     0.
% 1.18/1.00  
% 1.18/1.00  sup_num_of_clauses:                     33
% 1.18/1.00  sup_num_in_active:                      26
% 1.18/1.00  sup_num_in_passive:                     7
% 1.18/1.00  sup_num_of_loops:                       25
% 1.18/1.00  sup_fw_superposition:                   9
% 1.18/1.00  sup_bw_superposition:                   6
% 1.18/1.00  sup_immediate_simplified:               0
% 1.18/1.00  sup_given_eliminated:                   0
% 1.18/1.00  comparisons_done:                       0
% 1.18/1.00  comparisons_avoided:                    0
% 1.18/1.00  
% 1.18/1.00  ------ Simplifications
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  sim_fw_subset_subsumed:                 0
% 1.18/1.00  sim_bw_subset_subsumed:                 0
% 1.18/1.00  sim_fw_subsumed:                        0
% 1.18/1.00  sim_bw_subsumed:                        0
% 1.18/1.00  sim_fw_subsumption_res:                 0
% 1.18/1.00  sim_bw_subsumption_res:                 0
% 1.18/1.00  sim_tautology_del:                      2
% 1.18/1.00  sim_eq_tautology_del:                   0
% 1.18/1.00  sim_eq_res_simp:                        0
% 1.18/1.00  sim_fw_demodulated:                     0
% 1.18/1.00  sim_bw_demodulated:                     0
% 1.18/1.00  sim_light_normalised:                   0
% 1.18/1.00  sim_joinable_taut:                      0
% 1.18/1.00  sim_joinable_simp:                      0
% 1.18/1.00  sim_ac_normalised:                      0
% 1.18/1.00  sim_smt_subsumption:                    0
% 1.18/1.00  
%------------------------------------------------------------------------------

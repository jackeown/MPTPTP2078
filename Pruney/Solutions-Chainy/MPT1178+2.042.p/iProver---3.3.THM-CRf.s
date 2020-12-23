%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:05 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 319 expanded)
%              Number of clauses        :   66 (  85 expanded)
%              Number of leaves         :   22 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  582 (1623 expanded)
%              Number of equality atoms :  128 ( 306 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK7))
        & m1_orders_1(sK7,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK6,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK6))) )
      & l1_orders_2(sK6)
      & v5_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK6,sK7))
    & m1_orders_1(sK7,k1_orders_1(u1_struct_0(sK6)))
    & l1_orders_2(sK6)
    & v5_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f35,f56,f55])).

fof(f95,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK6,sK7)) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f42])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f36])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( ~ r1_xboole_0(X2,X0)
        & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
      & ( ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
      & ( ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | r1_xboole_0(X2,X0)
            | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
          & ( ( ~ r1_xboole_0(X2,X0)
              & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK2(X0))
            | r1_xboole_0(X2,X0)
            | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
          & ( ( ~ r1_xboole_0(X2,X0)
              & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
            | ~ r2_hidden(X2,sK2(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK2(X0))
        | r1_xboole_0(X2,X0)
        | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
      & ( ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
        | ~ r2_hidden(X2,sK2(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ r1_xboole_0(X2,X0)
      | ~ r2_hidden(X2,sK2(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f88,f86])).

fof(f94,plain,(
    m1_orders_1(sK7,k1_orders_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f57])).

fof(f104,plain,(
    m1_orders_1(sK7,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))) ),
    inference(definition_unfolding,[],[f94,f86])).

fof(f93,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f87,f86])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK5(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( m2_orders_2(sK5(X0,X1,X2),X0,X1)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK5(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK5(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK5(X0,X1,X2),X0,X1)
                    | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f52,f53])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f82,f86])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f65])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK6,sK7)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_13,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2478,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3139,plain,
    ( r1_tarski(k4_orders_2(sK6,sK7),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_2478])).

cnf(c_14,plain,
    ( k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2479,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4074,plain,
    ( k1_tarski(k1_xboole_0) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_2479])).

cnf(c_4078,plain,
    ( k1_zfmisc_1(k1_xboole_0) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4074,c_14])).

cnf(c_4089,plain,
    ( k4_orders_2(sK6,sK7) = k1_zfmisc_1(k1_xboole_0)
    | k4_orders_2(sK6,sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3139,c_4078])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2488,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X0,sK2(X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_450,plain,
    ( ~ r2_hidden(X0,sK2(X1))
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_451,plain,
    ( ~ r2_hidden(X0,sK2(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_2472,plain,
    ( r2_hidden(X0,sK2(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_3610,plain,
    ( sK2(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2488,c_2472])).

cnf(c_28,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_30,negated_conjecture,
    ( m1_orders_1(sK7,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_720,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_721,plain,
    ( ~ m2_orders_2(X0,X1,sK7)
    | r2_hidden(k1_funct_1(sK7,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_996,plain,
    ( ~ m2_orders_2(X0,X1,sK7)
    | r2_hidden(k1_funct_1(sK7,u1_struct_0(X1)),X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_721,c_31])).

cnf(c_997,plain,
    ( ~ m2_orders_2(X0,sK6,sK7)
    | r2_hidden(k1_funct_1(sK7,u1_struct_0(sK6)),X0)
    | v2_struct_0(sK6)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_996])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,negated_conjecture,
    ( v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_33,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1001,plain,
    ( ~ m2_orders_2(X0,sK6,sK7)
    | r2_hidden(k1_funct_1(sK7,u1_struct_0(sK6)),X0)
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_997,c_35,c_34,c_33,c_32])).

cnf(c_1283,plain,
    ( ~ m2_orders_2(X0,sK6,sK7)
    | r2_hidden(k1_funct_1(sK7,u1_struct_0(sK6)),X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_1001])).

cnf(c_2471,plain,
    ( m2_orders_2(X0,sK6,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK7,u1_struct_0(sK6)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1283])).

cnf(c_2984,plain,
    ( m2_orders_2(sK2(k1_xboole_0),sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_2472])).

cnf(c_3761,plain,
    ( m2_orders_2(k1_xboole_0,sK6,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3610,c_2984])).

cnf(c_1866,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2700,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_3270,plain,
    ( r2_hidden(X0,k4_orders_2(sK6,sK7))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2))
    | X0 != X1
    | k4_orders_2(sK6,sK7) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_2700])).

cnf(c_3271,plain,
    ( X0 != X1
    | k4_orders_2(sK6,sK7) != k1_zfmisc_1(X2)
    | r2_hidden(X0,k4_orders_2(sK6,sK7)) = iProver_top
    | r2_hidden(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3270])).

cnf(c_3273,plain,
    ( k4_orders_2(sK6,sK7) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | r2_hidden(k1_xboole_0,k4_orders_2(sK6,sK7)) = iProver_top
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3271])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_810,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,X1))
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_811,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,sK7))
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_892,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_xboole_0(k4_orders_2(X0,sK7))
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_811,c_31])).

cnf(c_893,plain,
    ( v2_struct_0(sK6)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v1_xboole_0(k4_orders_2(sK6,sK7))
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_892])).

cnf(c_895,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK6,sK7))
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_893,c_35,c_34,c_33,c_32])).

cnf(c_1303,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK6,sK7)) ),
    inference(equality_resolution_simp,[status(thm)],[c_895])).

cnf(c_1589,plain,
    ( k4_orders_2(sK6,sK7) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1303])).

cnf(c_26,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_750,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_751,plain,
    ( m2_orders_2(X0,X1,sK7)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK7))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_975,plain,
    ( m2_orders_2(X0,X1,sK7)
    | ~ r2_hidden(X0,k4_orders_2(X1,sK7))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_751,c_31])).

cnf(c_976,plain,
    ( m2_orders_2(X0,sK6,sK7)
    | ~ r2_hidden(X0,k4_orders_2(sK6,sK7))
    | v2_struct_0(sK6)
    | ~ v3_orders_2(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v5_orders_2(sK6)
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_980,plain,
    ( m2_orders_2(X0,sK6,sK7)
    | ~ r2_hidden(X0,k4_orders_2(sK6,sK7))
    | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_976,c_35,c_34,c_33,c_32])).

cnf(c_1287,plain,
    ( m2_orders_2(X0,sK6,sK7)
    | ~ r2_hidden(X0,k4_orders_2(sK6,sK7)) ),
    inference(equality_resolution_simp,[status(thm)],[c_980])).

cnf(c_1288,plain,
    ( m2_orders_2(X0,sK6,sK7) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_1290,plain,
    ( m2_orders_2(k1_xboole_0,sK6,sK7) = iProver_top
    | r2_hidden(k1_xboole_0,k4_orders_2(sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1288])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_114,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_107,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_97,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_99,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4089,c_3761,c_3273,c_1589,c_1290,c_0,c_114,c_107,c_99])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:16:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.44/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/0.97  
% 2.44/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/0.97  
% 2.44/0.97  ------  iProver source info
% 2.44/0.97  
% 2.44/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.44/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/0.97  git: non_committed_changes: false
% 2.44/0.97  git: last_make_outside_of_git: false
% 2.44/0.97  
% 2.44/0.97  ------ 
% 2.44/0.97  
% 2.44/0.97  ------ Input Options
% 2.44/0.97  
% 2.44/0.97  --out_options                           all
% 2.44/0.97  --tptp_safe_out                         true
% 2.44/0.97  --problem_path                          ""
% 2.44/0.97  --include_path                          ""
% 2.44/0.97  --clausifier                            res/vclausify_rel
% 2.44/0.97  --clausifier_options                    --mode clausify
% 2.44/0.97  --stdin                                 false
% 2.44/0.97  --stats_out                             all
% 2.44/0.97  
% 2.44/0.97  ------ General Options
% 2.44/0.97  
% 2.44/0.97  --fof                                   false
% 2.44/0.97  --time_out_real                         305.
% 2.44/0.97  --time_out_virtual                      -1.
% 2.44/0.97  --symbol_type_check                     false
% 2.44/0.97  --clausify_out                          false
% 2.44/0.97  --sig_cnt_out                           false
% 2.44/0.97  --trig_cnt_out                          false
% 2.44/0.97  --trig_cnt_out_tolerance                1.
% 2.44/0.97  --trig_cnt_out_sk_spl                   false
% 2.44/0.97  --abstr_cl_out                          false
% 2.44/0.97  
% 2.44/0.97  ------ Global Options
% 2.44/0.97  
% 2.44/0.97  --schedule                              default
% 2.44/0.97  --add_important_lit                     false
% 2.44/0.97  --prop_solver_per_cl                    1000
% 2.44/0.97  --min_unsat_core                        false
% 2.44/0.97  --soft_assumptions                      false
% 2.44/0.97  --soft_lemma_size                       3
% 2.44/0.97  --prop_impl_unit_size                   0
% 2.44/0.97  --prop_impl_unit                        []
% 2.44/0.97  --share_sel_clauses                     true
% 2.44/0.97  --reset_solvers                         false
% 2.44/0.97  --bc_imp_inh                            [conj_cone]
% 2.44/0.97  --conj_cone_tolerance                   3.
% 2.44/0.97  --extra_neg_conj                        none
% 2.44/0.97  --large_theory_mode                     true
% 2.44/0.97  --prolific_symb_bound                   200
% 2.44/0.97  --lt_threshold                          2000
% 2.44/0.97  --clause_weak_htbl                      true
% 2.44/0.97  --gc_record_bc_elim                     false
% 2.44/0.97  
% 2.44/0.97  ------ Preprocessing Options
% 2.44/0.97  
% 2.44/0.97  --preprocessing_flag                    true
% 2.44/0.97  --time_out_prep_mult                    0.1
% 2.44/0.97  --splitting_mode                        input
% 2.44/0.97  --splitting_grd                         true
% 2.44/0.97  --splitting_cvd                         false
% 2.44/0.97  --splitting_cvd_svl                     false
% 2.44/0.97  --splitting_nvd                         32
% 2.44/0.97  --sub_typing                            true
% 2.44/0.97  --prep_gs_sim                           true
% 2.44/0.97  --prep_unflatten                        true
% 2.44/0.97  --prep_res_sim                          true
% 2.44/0.97  --prep_upred                            true
% 2.44/0.97  --prep_sem_filter                       exhaustive
% 2.44/0.97  --prep_sem_filter_out                   false
% 2.44/0.97  --pred_elim                             true
% 2.44/0.97  --res_sim_input                         true
% 2.44/0.97  --eq_ax_congr_red                       true
% 2.44/0.97  --pure_diseq_elim                       true
% 2.44/0.97  --brand_transform                       false
% 2.44/0.97  --non_eq_to_eq                          false
% 2.44/0.97  --prep_def_merge                        true
% 2.44/0.97  --prep_def_merge_prop_impl              false
% 2.44/0.97  --prep_def_merge_mbd                    true
% 2.44/0.97  --prep_def_merge_tr_red                 false
% 2.44/0.97  --prep_def_merge_tr_cl                  false
% 2.44/0.97  --smt_preprocessing                     true
% 2.44/0.97  --smt_ac_axioms                         fast
% 2.44/0.97  --preprocessed_out                      false
% 2.44/0.97  --preprocessed_stats                    false
% 2.44/0.97  
% 2.44/0.97  ------ Abstraction refinement Options
% 2.44/0.97  
% 2.44/0.97  --abstr_ref                             []
% 2.44/0.97  --abstr_ref_prep                        false
% 2.44/0.97  --abstr_ref_until_sat                   false
% 2.44/0.97  --abstr_ref_sig_restrict                funpre
% 2.44/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.97  --abstr_ref_under                       []
% 2.44/0.97  
% 2.44/0.97  ------ SAT Options
% 2.44/0.97  
% 2.44/0.97  --sat_mode                              false
% 2.44/0.97  --sat_fm_restart_options                ""
% 2.44/0.97  --sat_gr_def                            false
% 2.44/0.97  --sat_epr_types                         true
% 2.44/0.97  --sat_non_cyclic_types                  false
% 2.44/0.97  --sat_finite_models                     false
% 2.44/0.97  --sat_fm_lemmas                         false
% 2.44/0.97  --sat_fm_prep                           false
% 2.44/0.97  --sat_fm_uc_incr                        true
% 2.44/0.97  --sat_out_model                         small
% 2.44/0.97  --sat_out_clauses                       false
% 2.44/0.97  
% 2.44/0.97  ------ QBF Options
% 2.44/0.97  
% 2.44/0.97  --qbf_mode                              false
% 2.44/0.97  --qbf_elim_univ                         false
% 2.44/0.97  --qbf_dom_inst                          none
% 2.44/0.97  --qbf_dom_pre_inst                      false
% 2.44/0.97  --qbf_sk_in                             false
% 2.44/0.97  --qbf_pred_elim                         true
% 2.44/0.97  --qbf_split                             512
% 2.44/0.97  
% 2.44/0.97  ------ BMC1 Options
% 2.44/0.97  
% 2.44/0.97  --bmc1_incremental                      false
% 2.44/0.97  --bmc1_axioms                           reachable_all
% 2.44/0.97  --bmc1_min_bound                        0
% 2.44/0.97  --bmc1_max_bound                        -1
% 2.44/0.97  --bmc1_max_bound_default                -1
% 2.44/0.97  --bmc1_symbol_reachability              true
% 2.44/0.97  --bmc1_property_lemmas                  false
% 2.44/0.97  --bmc1_k_induction                      false
% 2.44/0.97  --bmc1_non_equiv_states                 false
% 2.44/0.97  --bmc1_deadlock                         false
% 2.44/0.97  --bmc1_ucm                              false
% 2.44/0.97  --bmc1_add_unsat_core                   none
% 2.44/0.97  --bmc1_unsat_core_children              false
% 2.44/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.97  --bmc1_out_stat                         full
% 2.44/0.97  --bmc1_ground_init                      false
% 2.44/0.97  --bmc1_pre_inst_next_state              false
% 2.44/0.97  --bmc1_pre_inst_state                   false
% 2.44/0.97  --bmc1_pre_inst_reach_state             false
% 2.44/0.97  --bmc1_out_unsat_core                   false
% 2.44/0.97  --bmc1_aig_witness_out                  false
% 2.44/0.97  --bmc1_verbose                          false
% 2.44/0.97  --bmc1_dump_clauses_tptp                false
% 2.44/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.97  --bmc1_dump_file                        -
% 2.44/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.97  --bmc1_ucm_extend_mode                  1
% 2.44/0.97  --bmc1_ucm_init_mode                    2
% 2.44/0.97  --bmc1_ucm_cone_mode                    none
% 2.44/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.97  --bmc1_ucm_relax_model                  4
% 2.44/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.97  --bmc1_ucm_layered_model                none
% 2.44/0.97  --bmc1_ucm_max_lemma_size               10
% 2.44/0.97  
% 2.44/0.97  ------ AIG Options
% 2.44/0.97  
% 2.44/0.97  --aig_mode                              false
% 2.44/0.97  
% 2.44/0.97  ------ Instantiation Options
% 2.44/0.97  
% 2.44/0.97  --instantiation_flag                    true
% 2.44/0.97  --inst_sos_flag                         false
% 2.44/0.97  --inst_sos_phase                        true
% 2.44/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.97  --inst_lit_sel_side                     num_symb
% 2.44/0.97  --inst_solver_per_active                1400
% 2.44/0.97  --inst_solver_calls_frac                1.
% 2.44/0.97  --inst_passive_queue_type               priority_queues
% 2.44/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.97  --inst_passive_queues_freq              [25;2]
% 2.44/0.97  --inst_dismatching                      true
% 2.44/0.97  --inst_eager_unprocessed_to_passive     true
% 2.44/0.97  --inst_prop_sim_given                   true
% 2.44/0.97  --inst_prop_sim_new                     false
% 2.44/0.97  --inst_subs_new                         false
% 2.44/0.97  --inst_eq_res_simp                      false
% 2.44/0.97  --inst_subs_given                       false
% 2.44/0.97  --inst_orphan_elimination               true
% 2.44/0.97  --inst_learning_loop_flag               true
% 2.44/0.97  --inst_learning_start                   3000
% 2.44/0.97  --inst_learning_factor                  2
% 2.44/0.97  --inst_start_prop_sim_after_learn       3
% 2.44/0.97  --inst_sel_renew                        solver
% 2.44/0.97  --inst_lit_activity_flag                true
% 2.44/0.97  --inst_restr_to_given                   false
% 2.44/0.97  --inst_activity_threshold               500
% 2.44/0.97  --inst_out_proof                        true
% 2.44/0.97  
% 2.44/0.97  ------ Resolution Options
% 2.44/0.97  
% 2.44/0.97  --resolution_flag                       true
% 2.44/0.97  --res_lit_sel                           adaptive
% 2.44/0.97  --res_lit_sel_side                      none
% 2.44/0.97  --res_ordering                          kbo
% 2.44/0.97  --res_to_prop_solver                    active
% 2.44/0.97  --res_prop_simpl_new                    false
% 2.44/0.97  --res_prop_simpl_given                  true
% 2.44/0.97  --res_passive_queue_type                priority_queues
% 2.44/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.97  --res_passive_queues_freq               [15;5]
% 2.44/0.97  --res_forward_subs                      full
% 2.44/0.97  --res_backward_subs                     full
% 2.44/0.97  --res_forward_subs_resolution           true
% 2.44/0.97  --res_backward_subs_resolution          true
% 2.44/0.97  --res_orphan_elimination                true
% 2.44/0.97  --res_time_limit                        2.
% 2.44/0.97  --res_out_proof                         true
% 2.44/0.97  
% 2.44/0.97  ------ Superposition Options
% 2.44/0.97  
% 2.44/0.97  --superposition_flag                    true
% 2.44/0.97  --sup_passive_queue_type                priority_queues
% 2.44/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.97  --demod_completeness_check              fast
% 2.44/0.97  --demod_use_ground                      true
% 2.44/0.97  --sup_to_prop_solver                    passive
% 2.44/0.97  --sup_prop_simpl_new                    true
% 2.44/0.97  --sup_prop_simpl_given                  true
% 2.44/0.97  --sup_fun_splitting                     false
% 2.44/0.97  --sup_smt_interval                      50000
% 2.44/0.97  
% 2.44/0.97  ------ Superposition Simplification Setup
% 2.44/0.97  
% 2.44/0.97  --sup_indices_passive                   []
% 2.44/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.97  --sup_full_bw                           [BwDemod]
% 2.44/0.97  --sup_immed_triv                        [TrivRules]
% 2.44/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.97  --sup_immed_bw_main                     []
% 2.44/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.97  
% 2.44/0.97  ------ Combination Options
% 2.44/0.97  
% 2.44/0.97  --comb_res_mult                         3
% 2.44/0.97  --comb_sup_mult                         2
% 2.44/0.97  --comb_inst_mult                        10
% 2.44/0.97  
% 2.44/0.97  ------ Debug Options
% 2.44/0.97  
% 2.44/0.97  --dbg_backtrace                         false
% 2.44/0.97  --dbg_dump_prop_clauses                 false
% 2.44/0.97  --dbg_dump_prop_clauses_file            -
% 2.44/0.97  --dbg_out_stat                          false
% 2.44/0.97  ------ Parsing...
% 2.44/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/0.97  
% 2.44/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.44/0.97  
% 2.44/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/0.97  
% 2.44/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/0.97  ------ Proving...
% 2.44/0.97  ------ Problem Properties 
% 2.44/0.97  
% 2.44/0.97  
% 2.44/0.97  clauses                                 28
% 2.44/0.97  conjectures                             1
% 2.44/0.97  EPR                                     3
% 2.44/0.97  Horn                                    20
% 2.44/0.97  unary                                   11
% 2.44/0.97  binary                                  8
% 2.44/0.97  lits                                    56
% 2.44/0.97  lits eq                                 16
% 2.44/0.97  fd_pure                                 0
% 2.44/0.97  fd_pseudo                               0
% 2.44/0.97  fd_cond                                 4
% 2.44/0.97  fd_pseudo_cond                          3
% 2.44/0.97  AC symbols                              0
% 2.44/0.97  
% 2.44/0.97  ------ Schedule dynamic 5 is on 
% 2.44/0.97  
% 2.44/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/0.97  
% 2.44/0.97  
% 2.44/0.97  ------ 
% 2.44/0.97  Current options:
% 2.44/0.97  ------ 
% 2.44/0.97  
% 2.44/0.97  ------ Input Options
% 2.44/0.97  
% 2.44/0.97  --out_options                           all
% 2.44/0.97  --tptp_safe_out                         true
% 2.44/0.97  --problem_path                          ""
% 2.44/0.97  --include_path                          ""
% 2.44/0.97  --clausifier                            res/vclausify_rel
% 2.44/0.97  --clausifier_options                    --mode clausify
% 2.44/0.97  --stdin                                 false
% 2.44/0.97  --stats_out                             all
% 2.44/0.97  
% 2.44/0.97  ------ General Options
% 2.44/0.97  
% 2.44/0.97  --fof                                   false
% 2.44/0.97  --time_out_real                         305.
% 2.44/0.97  --time_out_virtual                      -1.
% 2.44/0.97  --symbol_type_check                     false
% 2.44/0.97  --clausify_out                          false
% 2.44/0.97  --sig_cnt_out                           false
% 2.44/0.97  --trig_cnt_out                          false
% 2.44/0.97  --trig_cnt_out_tolerance                1.
% 2.44/0.97  --trig_cnt_out_sk_spl                   false
% 2.44/0.97  --abstr_cl_out                          false
% 2.44/0.97  
% 2.44/0.97  ------ Global Options
% 2.44/0.97  
% 2.44/0.97  --schedule                              default
% 2.44/0.97  --add_important_lit                     false
% 2.44/0.97  --prop_solver_per_cl                    1000
% 2.44/0.97  --min_unsat_core                        false
% 2.44/0.97  --soft_assumptions                      false
% 2.44/0.97  --soft_lemma_size                       3
% 2.44/0.97  --prop_impl_unit_size                   0
% 2.44/0.97  --prop_impl_unit                        []
% 2.44/0.97  --share_sel_clauses                     true
% 2.44/0.97  --reset_solvers                         false
% 2.44/0.97  --bc_imp_inh                            [conj_cone]
% 2.44/0.97  --conj_cone_tolerance                   3.
% 2.44/0.97  --extra_neg_conj                        none
% 2.44/0.97  --large_theory_mode                     true
% 2.44/0.97  --prolific_symb_bound                   200
% 2.44/0.97  --lt_threshold                          2000
% 2.44/0.97  --clause_weak_htbl                      true
% 2.44/0.97  --gc_record_bc_elim                     false
% 2.44/0.97  
% 2.44/0.97  ------ Preprocessing Options
% 2.44/0.97  
% 2.44/0.97  --preprocessing_flag                    true
% 2.44/0.97  --time_out_prep_mult                    0.1
% 2.44/0.97  --splitting_mode                        input
% 2.44/0.97  --splitting_grd                         true
% 2.44/0.97  --splitting_cvd                         false
% 2.44/0.97  --splitting_cvd_svl                     false
% 2.44/0.97  --splitting_nvd                         32
% 2.44/0.97  --sub_typing                            true
% 2.44/0.97  --prep_gs_sim                           true
% 2.44/0.97  --prep_unflatten                        true
% 2.44/0.97  --prep_res_sim                          true
% 2.44/0.97  --prep_upred                            true
% 2.44/0.97  --prep_sem_filter                       exhaustive
% 2.44/0.97  --prep_sem_filter_out                   false
% 2.44/0.97  --pred_elim                             true
% 2.44/0.97  --res_sim_input                         true
% 2.44/0.97  --eq_ax_congr_red                       true
% 2.44/0.97  --pure_diseq_elim                       true
% 2.44/0.97  --brand_transform                       false
% 2.44/0.97  --non_eq_to_eq                          false
% 2.44/0.97  --prep_def_merge                        true
% 2.44/0.97  --prep_def_merge_prop_impl              false
% 2.44/0.97  --prep_def_merge_mbd                    true
% 2.44/0.97  --prep_def_merge_tr_red                 false
% 2.44/0.97  --prep_def_merge_tr_cl                  false
% 2.44/0.97  --smt_preprocessing                     true
% 2.44/0.97  --smt_ac_axioms                         fast
% 2.44/0.97  --preprocessed_out                      false
% 2.44/0.97  --preprocessed_stats                    false
% 2.44/0.97  
% 2.44/0.97  ------ Abstraction refinement Options
% 2.44/0.97  
% 2.44/0.97  --abstr_ref                             []
% 2.44/0.97  --abstr_ref_prep                        false
% 2.44/0.97  --abstr_ref_until_sat                   false
% 2.44/0.97  --abstr_ref_sig_restrict                funpre
% 2.44/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.97  --abstr_ref_under                       []
% 2.44/0.97  
% 2.44/0.97  ------ SAT Options
% 2.44/0.97  
% 2.44/0.97  --sat_mode                              false
% 2.44/0.97  --sat_fm_restart_options                ""
% 2.44/0.97  --sat_gr_def                            false
% 2.44/0.97  --sat_epr_types                         true
% 2.44/0.97  --sat_non_cyclic_types                  false
% 2.44/0.97  --sat_finite_models                     false
% 2.44/0.97  --sat_fm_lemmas                         false
% 2.44/0.97  --sat_fm_prep                           false
% 2.44/0.97  --sat_fm_uc_incr                        true
% 2.44/0.97  --sat_out_model                         small
% 2.44/0.97  --sat_out_clauses                       false
% 2.44/0.97  
% 2.44/0.97  ------ QBF Options
% 2.44/0.97  
% 2.44/0.97  --qbf_mode                              false
% 2.44/0.97  --qbf_elim_univ                         false
% 2.44/0.97  --qbf_dom_inst                          none
% 2.44/0.97  --qbf_dom_pre_inst                      false
% 2.44/0.97  --qbf_sk_in                             false
% 2.44/0.97  --qbf_pred_elim                         true
% 2.44/0.97  --qbf_split                             512
% 2.44/0.97  
% 2.44/0.97  ------ BMC1 Options
% 2.44/0.97  
% 2.44/0.97  --bmc1_incremental                      false
% 2.44/0.97  --bmc1_axioms                           reachable_all
% 2.44/0.97  --bmc1_min_bound                        0
% 2.44/0.97  --bmc1_max_bound                        -1
% 2.44/0.97  --bmc1_max_bound_default                -1
% 2.44/0.97  --bmc1_symbol_reachability              true
% 2.44/0.97  --bmc1_property_lemmas                  false
% 2.44/0.97  --bmc1_k_induction                      false
% 2.44/0.97  --bmc1_non_equiv_states                 false
% 2.44/0.97  --bmc1_deadlock                         false
% 2.44/0.97  --bmc1_ucm                              false
% 2.44/0.97  --bmc1_add_unsat_core                   none
% 2.44/0.97  --bmc1_unsat_core_children              false
% 2.44/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.97  --bmc1_out_stat                         full
% 2.44/0.97  --bmc1_ground_init                      false
% 2.44/0.97  --bmc1_pre_inst_next_state              false
% 2.44/0.97  --bmc1_pre_inst_state                   false
% 2.44/0.97  --bmc1_pre_inst_reach_state             false
% 2.44/0.97  --bmc1_out_unsat_core                   false
% 2.44/0.97  --bmc1_aig_witness_out                  false
% 2.44/0.97  --bmc1_verbose                          false
% 2.44/0.97  --bmc1_dump_clauses_tptp                false
% 2.44/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.97  --bmc1_dump_file                        -
% 2.44/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.97  --bmc1_ucm_extend_mode                  1
% 2.44/0.97  --bmc1_ucm_init_mode                    2
% 2.44/0.97  --bmc1_ucm_cone_mode                    none
% 2.44/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.97  --bmc1_ucm_relax_model                  4
% 2.44/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.97  --bmc1_ucm_layered_model                none
% 2.44/0.97  --bmc1_ucm_max_lemma_size               10
% 2.44/0.97  
% 2.44/0.97  ------ AIG Options
% 2.44/0.97  
% 2.44/0.97  --aig_mode                              false
% 2.44/0.97  
% 2.44/0.97  ------ Instantiation Options
% 2.44/0.97  
% 2.44/0.97  --instantiation_flag                    true
% 2.44/0.97  --inst_sos_flag                         false
% 2.44/0.97  --inst_sos_phase                        true
% 2.44/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.97  --inst_lit_sel_side                     none
% 2.44/0.97  --inst_solver_per_active                1400
% 2.44/0.97  --inst_solver_calls_frac                1.
% 2.44/0.97  --inst_passive_queue_type               priority_queues
% 2.44/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.97  --inst_passive_queues_freq              [25;2]
% 2.44/0.97  --inst_dismatching                      true
% 2.44/0.97  --inst_eager_unprocessed_to_passive     true
% 2.44/0.97  --inst_prop_sim_given                   true
% 2.44/0.97  --inst_prop_sim_new                     false
% 2.44/0.97  --inst_subs_new                         false
% 2.44/0.97  --inst_eq_res_simp                      false
% 2.44/0.97  --inst_subs_given                       false
% 2.44/0.97  --inst_orphan_elimination               true
% 2.44/0.97  --inst_learning_loop_flag               true
% 2.44/0.97  --inst_learning_start                   3000
% 2.44/0.97  --inst_learning_factor                  2
% 2.44/0.97  --inst_start_prop_sim_after_learn       3
% 2.44/0.97  --inst_sel_renew                        solver
% 2.44/0.97  --inst_lit_activity_flag                true
% 2.44/0.97  --inst_restr_to_given                   false
% 2.44/0.97  --inst_activity_threshold               500
% 2.44/0.97  --inst_out_proof                        true
% 2.44/0.97  
% 2.44/0.97  ------ Resolution Options
% 2.44/0.97  
% 2.44/0.97  --resolution_flag                       false
% 2.44/0.97  --res_lit_sel                           adaptive
% 2.44/0.97  --res_lit_sel_side                      none
% 2.44/0.97  --res_ordering                          kbo
% 2.44/0.97  --res_to_prop_solver                    active
% 2.44/0.97  --res_prop_simpl_new                    false
% 2.44/0.97  --res_prop_simpl_given                  true
% 2.44/0.97  --res_passive_queue_type                priority_queues
% 2.44/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.97  --res_passive_queues_freq               [15;5]
% 2.44/0.97  --res_forward_subs                      full
% 2.44/0.97  --res_backward_subs                     full
% 2.44/0.97  --res_forward_subs_resolution           true
% 2.44/0.97  --res_backward_subs_resolution          true
% 2.44/0.97  --res_orphan_elimination                true
% 2.44/0.97  --res_time_limit                        2.
% 2.44/0.97  --res_out_proof                         true
% 2.44/0.97  
% 2.44/0.97  ------ Superposition Options
% 2.44/0.97  
% 2.44/0.97  --superposition_flag                    true
% 2.44/0.97  --sup_passive_queue_type                priority_queues
% 2.44/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.97  --demod_completeness_check              fast
% 2.44/0.97  --demod_use_ground                      true
% 2.44/0.97  --sup_to_prop_solver                    passive
% 2.44/0.97  --sup_prop_simpl_new                    true
% 2.44/0.97  --sup_prop_simpl_given                  true
% 2.44/0.97  --sup_fun_splitting                     false
% 2.44/0.97  --sup_smt_interval                      50000
% 2.44/0.97  
% 2.44/0.97  ------ Superposition Simplification Setup
% 2.44/0.97  
% 2.44/0.97  --sup_indices_passive                   []
% 2.44/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.97  --sup_full_bw                           [BwDemod]
% 2.44/0.97  --sup_immed_triv                        [TrivRules]
% 2.44/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.97  --sup_immed_bw_main                     []
% 2.44/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.97  
% 2.44/0.97  ------ Combination Options
% 2.44/0.97  
% 2.44/0.97  --comb_res_mult                         3
% 2.44/0.97  --comb_sup_mult                         2
% 2.44/0.97  --comb_inst_mult                        10
% 2.44/0.97  
% 2.44/0.97  ------ Debug Options
% 2.44/0.97  
% 2.44/0.97  --dbg_backtrace                         false
% 2.44/0.97  --dbg_dump_prop_clauses                 false
% 2.44/0.97  --dbg_dump_prop_clauses_file            -
% 2.44/0.97  --dbg_out_stat                          false
% 2.44/0.97  
% 2.44/0.97  
% 2.44/0.97  
% 2.44/0.97  
% 2.44/0.97  ------ Proving...
% 2.44/0.97  
% 2.44/0.97  
% 2.44/0.97  % SZS status Theorem for theBenchmark.p
% 2.44/0.97  
% 2.44/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/0.97  
% 2.44/0.97  fof(f19,conjecture,(
% 2.44/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f20,negated_conjecture,(
% 2.44/0.97    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 2.44/0.97    inference(negated_conjecture,[],[f19])).
% 2.44/0.97  
% 2.44/0.97  fof(f34,plain,(
% 2.44/0.97    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.44/0.97    inference(ennf_transformation,[],[f20])).
% 2.44/0.97  
% 2.44/0.97  fof(f35,plain,(
% 2.44/0.97    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.44/0.97    inference(flattening,[],[f34])).
% 2.44/0.97  
% 2.44/0.97  fof(f56,plain,(
% 2.44/0.97    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK7)) & m1_orders_1(sK7,k1_orders_1(u1_struct_0(X0))))) )),
% 2.44/0.97    introduced(choice_axiom,[])).
% 2.44/0.97  
% 2.44/0.97  fof(f55,plain,(
% 2.44/0.97    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK6,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK6)))) & l1_orders_2(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6))),
% 2.44/0.97    introduced(choice_axiom,[])).
% 2.44/0.97  
% 2.44/0.97  fof(f57,plain,(
% 2.44/0.97    (k1_xboole_0 = k3_tarski(k4_orders_2(sK6,sK7)) & m1_orders_1(sK7,k1_orders_1(u1_struct_0(sK6)))) & l1_orders_2(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6)),
% 2.44/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f35,f56,f55])).
% 2.44/0.97  
% 2.44/0.97  fof(f95,plain,(
% 2.44/0.97    k1_xboole_0 = k3_tarski(k4_orders_2(sK6,sK7))),
% 2.44/0.97    inference(cnf_transformation,[],[f57])).
% 2.44/0.97  
% 2.44/0.97  fof(f10,axiom,(
% 2.44/0.97    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f72,plain,(
% 2.44/0.97    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 2.44/0.97    inference(cnf_transformation,[],[f10])).
% 2.44/0.97  
% 2.44/0.97  fof(f11,axiom,(
% 2.44/0.97    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f73,plain,(
% 2.44/0.97    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 2.44/0.97    inference(cnf_transformation,[],[f11])).
% 2.44/0.97  
% 2.44/0.97  fof(f8,axiom,(
% 2.44/0.97    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f42,plain,(
% 2.44/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.44/0.97    inference(nnf_transformation,[],[f8])).
% 2.44/0.97  
% 2.44/0.97  fof(f43,plain,(
% 2.44/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.44/0.97    inference(flattening,[],[f42])).
% 2.44/0.97  
% 2.44/0.97  fof(f68,plain,(
% 2.44/0.97    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.44/0.97    inference(cnf_transformation,[],[f43])).
% 2.44/0.97  
% 2.44/0.97  fof(f2,axiom,(
% 2.44/0.97    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f24,plain,(
% 2.44/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.44/0.97    inference(ennf_transformation,[],[f2])).
% 2.44/0.97  
% 2.44/0.97  fof(f36,plain,(
% 2.44/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.44/0.97    introduced(choice_axiom,[])).
% 2.44/0.97  
% 2.44/0.97  fof(f37,plain,(
% 2.44/0.97    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.44/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f36])).
% 2.44/0.97  
% 2.44/0.97  fof(f59,plain,(
% 2.44/0.97    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.44/0.97    inference(cnf_transformation,[],[f37])).
% 2.44/0.97  
% 2.44/0.97  fof(f5,axiom,(
% 2.44/0.97    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f62,plain,(
% 2.44/0.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.44/0.97    inference(cnf_transformation,[],[f5])).
% 2.44/0.97  
% 2.44/0.97  fof(f13,axiom,(
% 2.44/0.97    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))))),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f44,plain,(
% 2.44/0.97    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | (r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,X1)))),
% 2.44/0.97    inference(nnf_transformation,[],[f13])).
% 2.44/0.97  
% 2.44/0.97  fof(f45,plain,(
% 2.44/0.97    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,X1)))),
% 2.44/0.97    inference(flattening,[],[f44])).
% 2.44/0.97  
% 2.44/0.97  fof(f46,plain,(
% 2.44/0.97    ! [X0] : (? [X1] : ! [X2] : ((r2_hidden(X2,X1) | r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,X1))) => ! [X2] : ((r2_hidden(X2,sK2(X0)) | r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,sK2(X0)))))),
% 2.44/0.97    introduced(choice_axiom,[])).
% 2.44/0.97  
% 2.44/0.97  fof(f47,plain,(
% 2.44/0.97    ! [X0] : ! [X2] : ((r2_hidden(X2,sK2(X0)) | r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,sK2(X0))))),
% 2.44/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 2.44/0.97  
% 2.44/0.97  fof(f76,plain,(
% 2.44/0.97    ( ! [X2,X0] : (~r1_xboole_0(X2,X0) | ~r2_hidden(X2,sK2(X0))) )),
% 2.44/0.97    inference(cnf_transformation,[],[f47])).
% 2.44/0.97  
% 2.44/0.97  fof(f18,axiom,(
% 2.44/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f32,plain,(
% 2.44/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.44/0.97    inference(ennf_transformation,[],[f18])).
% 2.44/0.97  
% 2.44/0.97  fof(f33,plain,(
% 2.44/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/0.97    inference(flattening,[],[f32])).
% 2.44/0.97  
% 2.44/0.97  fof(f88,plain,(
% 2.44/0.97    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/0.97    inference(cnf_transformation,[],[f33])).
% 2.44/0.97  
% 2.44/0.97  fof(f16,axiom,(
% 2.44/0.97    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f86,plain,(
% 2.44/0.97    ( ! [X0] : (k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))) )),
% 2.44/0.97    inference(cnf_transformation,[],[f16])).
% 2.44/0.97  
% 2.44/0.97  fof(f103,plain,(
% 2.44/0.97    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/0.97    inference(definition_unfolding,[],[f88,f86])).
% 2.44/0.97  
% 2.44/0.97  fof(f94,plain,(
% 2.44/0.97    m1_orders_1(sK7,k1_orders_1(u1_struct_0(sK6)))),
% 2.44/0.97    inference(cnf_transformation,[],[f57])).
% 2.44/0.97  
% 2.44/0.97  fof(f104,plain,(
% 2.44/0.97    m1_orders_1(sK7,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)))),
% 2.44/0.97    inference(definition_unfolding,[],[f94,f86])).
% 2.44/0.97  
% 2.44/0.97  fof(f93,plain,(
% 2.44/0.97    l1_orders_2(sK6)),
% 2.44/0.97    inference(cnf_transformation,[],[f57])).
% 2.44/0.97  
% 2.44/0.97  fof(f89,plain,(
% 2.44/0.97    ~v2_struct_0(sK6)),
% 2.44/0.97    inference(cnf_transformation,[],[f57])).
% 2.44/0.97  
% 2.44/0.97  fof(f90,plain,(
% 2.44/0.97    v3_orders_2(sK6)),
% 2.44/0.97    inference(cnf_transformation,[],[f57])).
% 2.44/0.97  
% 2.44/0.97  fof(f91,plain,(
% 2.44/0.97    v4_orders_2(sK6)),
% 2.44/0.97    inference(cnf_transformation,[],[f57])).
% 2.44/0.97  
% 2.44/0.97  fof(f92,plain,(
% 2.44/0.97    v5_orders_2(sK6)),
% 2.44/0.97    inference(cnf_transformation,[],[f57])).
% 2.44/0.97  
% 2.44/0.97  fof(f1,axiom,(
% 2.44/0.97    v1_xboole_0(k1_xboole_0)),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f58,plain,(
% 2.44/0.97    v1_xboole_0(k1_xboole_0)),
% 2.44/0.97    inference(cnf_transformation,[],[f1])).
% 2.44/0.97  
% 2.44/0.97  fof(f17,axiom,(
% 2.44/0.97    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f30,plain,(
% 2.44/0.97    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.44/0.97    inference(ennf_transformation,[],[f17])).
% 2.44/0.97  
% 2.44/0.97  fof(f31,plain,(
% 2.44/0.97    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/0.97    inference(flattening,[],[f30])).
% 2.44/0.97  
% 2.44/0.97  fof(f87,plain,(
% 2.44/0.97    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/0.97    inference(cnf_transformation,[],[f31])).
% 2.44/0.97  
% 2.44/0.97  fof(f102,plain,(
% 2.44/0.97    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/0.97    inference(definition_unfolding,[],[f87,f86])).
% 2.44/0.97  
% 2.44/0.97  fof(f15,axiom,(
% 2.44/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f28,plain,(
% 2.44/0.97    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.44/0.97    inference(ennf_transformation,[],[f15])).
% 2.44/0.97  
% 2.44/0.97  fof(f29,plain,(
% 2.44/0.97    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/0.97    inference(flattening,[],[f28])).
% 2.44/0.97  
% 2.44/0.97  fof(f51,plain,(
% 2.44/0.97    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/0.97    inference(nnf_transformation,[],[f29])).
% 2.44/0.97  
% 2.44/0.97  fof(f52,plain,(
% 2.44/0.97    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/0.97    inference(rectify,[],[f51])).
% 2.44/0.97  
% 2.44/0.97  fof(f53,plain,(
% 2.44/0.97    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK5(X0,X1,X2),X0,X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (m2_orders_2(sK5(X0,X1,X2),X0,X1) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.44/0.97    introduced(choice_axiom,[])).
% 2.44/0.97  
% 2.44/0.97  fof(f54,plain,(
% 2.44/0.97    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK5(X0,X1,X2),X0,X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (m2_orders_2(sK5(X0,X1,X2),X0,X1) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f52,f53])).
% 2.44/0.97  
% 2.44/0.97  fof(f82,plain,(
% 2.44/0.97    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/0.97    inference(cnf_transformation,[],[f54])).
% 2.44/0.97  
% 2.44/0.97  fof(f101,plain,(
% 2.44/0.97    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/0.97    inference(definition_unfolding,[],[f82,f86])).
% 2.44/0.97  
% 2.44/0.97  fof(f110,plain,(
% 2.44/0.97    ( ! [X4,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/0.97    inference(equality_resolution,[],[f101])).
% 2.44/0.97  
% 2.44/0.97  fof(f4,axiom,(
% 2.44/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f61,plain,(
% 2.44/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.44/0.97    inference(cnf_transformation,[],[f4])).
% 2.44/0.97  
% 2.44/0.97  fof(f6,axiom,(
% 2.44/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f25,plain,(
% 2.44/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.44/0.97    inference(ennf_transformation,[],[f6])).
% 2.44/0.97  
% 2.44/0.97  fof(f63,plain,(
% 2.44/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.44/0.97    inference(cnf_transformation,[],[f25])).
% 2.44/0.97  
% 2.44/0.97  fof(f7,axiom,(
% 2.44/0.97    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.44/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.97  
% 2.44/0.97  fof(f38,plain,(
% 2.44/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.44/0.97    inference(nnf_transformation,[],[f7])).
% 2.44/0.97  
% 2.44/0.97  fof(f39,plain,(
% 2.44/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.44/0.97    inference(rectify,[],[f38])).
% 2.44/0.97  
% 2.44/0.97  fof(f40,plain,(
% 2.44/0.97    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.44/0.97    introduced(choice_axiom,[])).
% 2.44/0.97  
% 2.44/0.97  fof(f41,plain,(
% 2.44/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.44/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 2.44/0.97  
% 2.44/0.97  fof(f65,plain,(
% 2.44/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.44/0.97    inference(cnf_transformation,[],[f41])).
% 2.44/0.97  
% 2.44/0.97  fof(f105,plain,(
% 2.44/0.97    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.44/0.97    inference(equality_resolution,[],[f65])).
% 2.44/0.97  
% 2.44/0.97  cnf(c_29,negated_conjecture,
% 2.44/0.97      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK6,sK7)) ),
% 2.44/0.97      inference(cnf_transformation,[],[f95]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_13,plain,
% 2.44/0.97      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
% 2.44/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_2478,plain,
% 2.44/0.97      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
% 2.44/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_3139,plain,
% 2.44/0.97      ( r1_tarski(k4_orders_2(sK6,sK7),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.44/0.97      inference(superposition,[status(thm)],[c_29,c_2478]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_14,plain,
% 2.44/0.97      ( k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 2.44/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_12,plain,
% 2.44/0.97      ( ~ r1_tarski(X0,k1_tarski(X1))
% 2.44/0.97      | k1_tarski(X1) = X0
% 2.44/0.97      | k1_xboole_0 = X0 ),
% 2.44/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_2479,plain,
% 2.44/0.97      ( k1_tarski(X0) = X1
% 2.44/0.97      | k1_xboole_0 = X1
% 2.44/0.97      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 2.44/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_4074,plain,
% 2.44/0.97      ( k1_tarski(k1_xboole_0) = X0
% 2.44/0.97      | k1_xboole_0 = X0
% 2.44/0.97      | r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/0.97      inference(superposition,[status(thm)],[c_14,c_2479]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_4078,plain,
% 2.44/0.97      ( k1_zfmisc_1(k1_xboole_0) = X0
% 2.44/0.97      | k1_xboole_0 = X0
% 2.44/0.97      | r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/0.97      inference(demodulation,[status(thm)],[c_4074,c_14]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_4089,plain,
% 2.44/0.97      ( k4_orders_2(sK6,sK7) = k1_zfmisc_1(k1_xboole_0)
% 2.44/0.97      | k4_orders_2(sK6,sK7) = k1_xboole_0 ),
% 2.44/0.97      inference(superposition,[status(thm)],[c_3139,c_4078]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_1,plain,
% 2.44/0.97      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.44/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_2488,plain,
% 2.44/0.97      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.44/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_4,plain,
% 2.44/0.97      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.44/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_17,plain,
% 2.44/0.97      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X0,sK2(X1)) ),
% 2.44/0.97      inference(cnf_transformation,[],[f76]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_450,plain,
% 2.44/0.97      ( ~ r2_hidden(X0,sK2(X1)) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.44/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_451,plain,
% 2.44/0.97      ( ~ r2_hidden(X0,sK2(k1_xboole_0)) ),
% 2.44/0.97      inference(unflattening,[status(thm)],[c_450]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_2472,plain,
% 2.44/0.97      ( r2_hidden(X0,sK2(k1_xboole_0)) != iProver_top ),
% 2.44/0.97      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_3610,plain,
% 2.44/0.97      ( sK2(k1_xboole_0) = k1_xboole_0 ),
% 2.44/0.97      inference(superposition,[status(thm)],[c_2488,c_2472]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_28,plain,
% 2.44/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 2.44/0.97      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 2.44/0.97      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 2.44/0.97      | v2_struct_0(X1)
% 2.44/0.97      | ~ v3_orders_2(X1)
% 2.44/0.97      | ~ v4_orders_2(X1)
% 2.44/0.97      | ~ v5_orders_2(X1)
% 2.44/0.97      | ~ l1_orders_2(X1) ),
% 2.44/0.97      inference(cnf_transformation,[],[f103]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_30,negated_conjecture,
% 2.44/0.97      ( m1_orders_1(sK7,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))) ),
% 2.44/0.97      inference(cnf_transformation,[],[f104]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_720,plain,
% 2.44/0.97      ( ~ m2_orders_2(X0,X1,X2)
% 2.44/0.97      | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X0)
% 2.44/0.97      | v2_struct_0(X1)
% 2.44/0.97      | ~ v3_orders_2(X1)
% 2.44/0.97      | ~ v4_orders_2(X1)
% 2.44/0.97      | ~ v5_orders_2(X1)
% 2.44/0.97      | ~ l1_orders_2(X1)
% 2.44/0.97      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
% 2.44/0.97      | sK7 != X2 ),
% 2.44/0.97      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_721,plain,
% 2.44/0.97      ( ~ m2_orders_2(X0,X1,sK7)
% 2.44/0.97      | r2_hidden(k1_funct_1(sK7,u1_struct_0(X1)),X0)
% 2.44/0.97      | v2_struct_0(X1)
% 2.44/0.97      | ~ v3_orders_2(X1)
% 2.44/0.97      | ~ v4_orders_2(X1)
% 2.44/0.97      | ~ v5_orders_2(X1)
% 2.44/0.97      | ~ l1_orders_2(X1)
% 2.44/0.97      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
% 2.44/0.97      inference(unflattening,[status(thm)],[c_720]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_31,negated_conjecture,
% 2.44/0.97      ( l1_orders_2(sK6) ),
% 2.44/0.97      inference(cnf_transformation,[],[f93]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_996,plain,
% 2.44/0.97      ( ~ m2_orders_2(X0,X1,sK7)
% 2.44/0.97      | r2_hidden(k1_funct_1(sK7,u1_struct_0(X1)),X0)
% 2.44/0.97      | v2_struct_0(X1)
% 2.44/0.97      | ~ v3_orders_2(X1)
% 2.44/0.97      | ~ v4_orders_2(X1)
% 2.44/0.97      | ~ v5_orders_2(X1)
% 2.44/0.97      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
% 2.44/0.97      | sK6 != X1 ),
% 2.44/0.97      inference(resolution_lifted,[status(thm)],[c_721,c_31]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_997,plain,
% 2.44/0.97      ( ~ m2_orders_2(X0,sK6,sK7)
% 2.44/0.97      | r2_hidden(k1_funct_1(sK7,u1_struct_0(sK6)),X0)
% 2.44/0.97      | v2_struct_0(sK6)
% 2.44/0.97      | ~ v3_orders_2(sK6)
% 2.44/0.97      | ~ v4_orders_2(sK6)
% 2.44/0.97      | ~ v5_orders_2(sK6)
% 2.44/0.97      | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
% 2.44/0.97      inference(unflattening,[status(thm)],[c_996]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_35,negated_conjecture,
% 2.44/0.97      ( ~ v2_struct_0(sK6) ),
% 2.44/0.97      inference(cnf_transformation,[],[f89]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_34,negated_conjecture,
% 2.44/0.97      ( v3_orders_2(sK6) ),
% 2.44/0.97      inference(cnf_transformation,[],[f90]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_33,negated_conjecture,
% 2.44/0.97      ( v4_orders_2(sK6) ),
% 2.44/0.97      inference(cnf_transformation,[],[f91]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_32,negated_conjecture,
% 2.44/0.97      ( v5_orders_2(sK6) ),
% 2.44/0.97      inference(cnf_transformation,[],[f92]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_1001,plain,
% 2.44/0.97      ( ~ m2_orders_2(X0,sK6,sK7)
% 2.44/0.97      | r2_hidden(k1_funct_1(sK7,u1_struct_0(sK6)),X0)
% 2.44/0.97      | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
% 2.44/0.97      inference(global_propositional_subsumption,
% 2.44/0.97                [status(thm)],
% 2.44/0.97                [c_997,c_35,c_34,c_33,c_32]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_1283,plain,
% 2.44/0.97      ( ~ m2_orders_2(X0,sK6,sK7)
% 2.44/0.97      | r2_hidden(k1_funct_1(sK7,u1_struct_0(sK6)),X0) ),
% 2.44/0.97      inference(equality_resolution_simp,[status(thm)],[c_1001]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_2471,plain,
% 2.44/0.97      ( m2_orders_2(X0,sK6,sK7) != iProver_top
% 2.44/0.97      | r2_hidden(k1_funct_1(sK7,u1_struct_0(sK6)),X0) = iProver_top ),
% 2.44/0.97      inference(predicate_to_equality,[status(thm)],[c_1283]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_2984,plain,
% 2.44/0.97      ( m2_orders_2(sK2(k1_xboole_0),sK6,sK7) != iProver_top ),
% 2.44/0.97      inference(superposition,[status(thm)],[c_2471,c_2472]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_3761,plain,
% 2.44/0.97      ( m2_orders_2(k1_xboole_0,sK6,sK7) != iProver_top ),
% 2.44/0.97      inference(demodulation,[status(thm)],[c_3610,c_2984]) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_1866,plain,
% 2.44/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.44/0.97      theory(equality) ).
% 2.44/0.97  
% 2.44/0.97  cnf(c_2700,plain,
% 2.44/0.97      ( r2_hidden(X0,X1)
% 2.44/0.98      | ~ r2_hidden(X2,k1_zfmisc_1(X3))
% 2.44/0.98      | X0 != X2
% 2.44/0.98      | X1 != k1_zfmisc_1(X3) ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_1866]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_3270,plain,
% 2.44/0.98      ( r2_hidden(X0,k4_orders_2(sK6,sK7))
% 2.44/0.98      | ~ r2_hidden(X1,k1_zfmisc_1(X2))
% 2.44/0.98      | X0 != X1
% 2.44/0.98      | k4_orders_2(sK6,sK7) != k1_zfmisc_1(X2) ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_2700]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_3271,plain,
% 2.44/0.98      ( X0 != X1
% 2.44/0.98      | k4_orders_2(sK6,sK7) != k1_zfmisc_1(X2)
% 2.44/0.98      | r2_hidden(X0,k4_orders_2(sK6,sK7)) = iProver_top
% 2.44/0.98      | r2_hidden(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_3270]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_3273,plain,
% 2.44/0.98      ( k4_orders_2(sK6,sK7) != k1_zfmisc_1(k1_xboole_0)
% 2.44/0.98      | k1_xboole_0 != k1_xboole_0
% 2.44/0.98      | r2_hidden(k1_xboole_0,k4_orders_2(sK6,sK7)) = iProver_top
% 2.44/0.98      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_3271]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_0,plain,
% 2.44/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.44/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_27,plain,
% 2.44/0.98      ( ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 2.44/0.98      | v2_struct_0(X1)
% 2.44/0.98      | ~ v3_orders_2(X1)
% 2.44/0.98      | ~ v4_orders_2(X1)
% 2.44/0.98      | ~ v5_orders_2(X1)
% 2.44/0.98      | ~ l1_orders_2(X1)
% 2.44/0.98      | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
% 2.44/0.98      inference(cnf_transformation,[],[f102]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_810,plain,
% 2.44/0.98      ( v2_struct_0(X0)
% 2.44/0.98      | ~ v3_orders_2(X0)
% 2.44/0.98      | ~ v4_orders_2(X0)
% 2.44/0.98      | ~ v5_orders_2(X0)
% 2.44/0.98      | ~ l1_orders_2(X0)
% 2.44/0.98      | ~ v1_xboole_0(k4_orders_2(X0,X1))
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
% 2.44/0.98      | sK7 != X1 ),
% 2.44/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_811,plain,
% 2.44/0.98      ( v2_struct_0(X0)
% 2.44/0.98      | ~ v3_orders_2(X0)
% 2.44/0.98      | ~ v4_orders_2(X0)
% 2.44/0.98      | ~ v5_orders_2(X0)
% 2.44/0.98      | ~ l1_orders_2(X0)
% 2.44/0.98      | ~ v1_xboole_0(k4_orders_2(X0,sK7))
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
% 2.44/0.98      inference(unflattening,[status(thm)],[c_810]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_892,plain,
% 2.44/0.98      ( v2_struct_0(X0)
% 2.44/0.98      | ~ v3_orders_2(X0)
% 2.44/0.98      | ~ v4_orders_2(X0)
% 2.44/0.98      | ~ v5_orders_2(X0)
% 2.44/0.98      | ~ v1_xboole_0(k4_orders_2(X0,sK7))
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
% 2.44/0.98      | sK6 != X0 ),
% 2.44/0.98      inference(resolution_lifted,[status(thm)],[c_811,c_31]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_893,plain,
% 2.44/0.98      ( v2_struct_0(sK6)
% 2.44/0.98      | ~ v3_orders_2(sK6)
% 2.44/0.98      | ~ v4_orders_2(sK6)
% 2.44/0.98      | ~ v5_orders_2(sK6)
% 2.44/0.98      | ~ v1_xboole_0(k4_orders_2(sK6,sK7))
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
% 2.44/0.98      inference(unflattening,[status(thm)],[c_892]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_895,plain,
% 2.44/0.98      ( ~ v1_xboole_0(k4_orders_2(sK6,sK7))
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
% 2.44/0.98      inference(global_propositional_subsumption,
% 2.44/0.98                [status(thm)],
% 2.44/0.98                [c_893,c_35,c_34,c_33,c_32]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1303,plain,
% 2.44/0.98      ( ~ v1_xboole_0(k4_orders_2(sK6,sK7)) ),
% 2.44/0.98      inference(equality_resolution_simp,[status(thm)],[c_895]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1589,plain,
% 2.44/0.98      ( k4_orders_2(sK6,sK7) != k1_xboole_0 ),
% 2.44/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_1303]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_26,plain,
% 2.44/0.98      ( m2_orders_2(X0,X1,X2)
% 2.44/0.98      | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))
% 2.44/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 2.44/0.98      | v2_struct_0(X1)
% 2.44/0.98      | ~ v3_orders_2(X1)
% 2.44/0.98      | ~ v4_orders_2(X1)
% 2.44/0.98      | ~ v5_orders_2(X1)
% 2.44/0.98      | ~ l1_orders_2(X1) ),
% 2.44/0.98      inference(cnf_transformation,[],[f110]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_750,plain,
% 2.44/0.98      ( m2_orders_2(X0,X1,X2)
% 2.44/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 2.44/0.98      | v2_struct_0(X1)
% 2.44/0.98      | ~ v3_orders_2(X1)
% 2.44/0.98      | ~ v4_orders_2(X1)
% 2.44/0.98      | ~ v5_orders_2(X1)
% 2.44/0.98      | ~ l1_orders_2(X1)
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
% 2.44/0.98      | sK7 != X2 ),
% 2.44/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_751,plain,
% 2.44/0.98      ( m2_orders_2(X0,X1,sK7)
% 2.44/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,sK7))
% 2.44/0.98      | v2_struct_0(X1)
% 2.44/0.98      | ~ v3_orders_2(X1)
% 2.44/0.98      | ~ v4_orders_2(X1)
% 2.44/0.98      | ~ v5_orders_2(X1)
% 2.44/0.98      | ~ l1_orders_2(X1)
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
% 2.44/0.98      inference(unflattening,[status(thm)],[c_750]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_975,plain,
% 2.44/0.98      ( m2_orders_2(X0,X1,sK7)
% 2.44/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,sK7))
% 2.44/0.98      | v2_struct_0(X1)
% 2.44/0.98      | ~ v3_orders_2(X1)
% 2.44/0.98      | ~ v4_orders_2(X1)
% 2.44/0.98      | ~ v5_orders_2(X1)
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0))
% 2.44/0.98      | sK6 != X1 ),
% 2.44/0.98      inference(resolution_lifted,[status(thm)],[c_751,c_31]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_976,plain,
% 2.44/0.98      ( m2_orders_2(X0,sK6,sK7)
% 2.44/0.98      | ~ r2_hidden(X0,k4_orders_2(sK6,sK7))
% 2.44/0.98      | v2_struct_0(sK6)
% 2.44/0.98      | ~ v3_orders_2(sK6)
% 2.44/0.98      | ~ v4_orders_2(sK6)
% 2.44/0.98      | ~ v5_orders_2(sK6)
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
% 2.44/0.98      inference(unflattening,[status(thm)],[c_975]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_980,plain,
% 2.44/0.98      ( m2_orders_2(X0,sK6,sK7)
% 2.44/0.98      | ~ r2_hidden(X0,k4_orders_2(sK6,sK7))
% 2.44/0.98      | k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) != k7_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),k9_setfam_1(u1_struct_0(sK6)),k1_tarski(k1_xboole_0)) ),
% 2.44/0.98      inference(global_propositional_subsumption,
% 2.44/0.98                [status(thm)],
% 2.44/0.98                [c_976,c_35,c_34,c_33,c_32]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1287,plain,
% 2.44/0.98      ( m2_orders_2(X0,sK6,sK7) | ~ r2_hidden(X0,k4_orders_2(sK6,sK7)) ),
% 2.44/0.98      inference(equality_resolution_simp,[status(thm)],[c_980]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1288,plain,
% 2.44/0.98      ( m2_orders_2(X0,sK6,sK7) = iProver_top
% 2.44/0.98      | r2_hidden(X0,k4_orders_2(sK6,sK7)) != iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_1287]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_1290,plain,
% 2.44/0.98      ( m2_orders_2(k1_xboole_0,sK6,sK7) = iProver_top
% 2.44/0.98      | r2_hidden(k1_xboole_0,k4_orders_2(sK6,sK7)) != iProver_top ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_1288]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_3,plain,
% 2.44/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 2.44/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_112,plain,
% 2.44/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_114,plain,
% 2.44/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_112]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_5,plain,
% 2.44/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.44/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_107,plain,
% 2.44/0.98      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_8,plain,
% 2.44/0.98      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.44/0.98      inference(cnf_transformation,[],[f105]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_97,plain,
% 2.44/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.44/0.98      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.44/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(c_99,plain,
% 2.44/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.44/0.98      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.44/0.98      inference(instantiation,[status(thm)],[c_97]) ).
% 2.44/0.98  
% 2.44/0.98  cnf(contradiction,plain,
% 2.44/0.98      ( $false ),
% 2.44/0.98      inference(minisat,
% 2.44/0.98                [status(thm)],
% 2.44/0.98                [c_4089,c_3761,c_3273,c_1589,c_1290,c_0,c_114,c_107,c_99]) ).
% 2.44/0.98  
% 2.44/0.98  
% 2.44/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/0.98  
% 2.44/0.98  ------                               Statistics
% 2.44/0.98  
% 2.44/0.98  ------ General
% 2.44/0.98  
% 2.44/0.98  abstr_ref_over_cycles:                  0
% 2.44/0.98  abstr_ref_under_cycles:                 0
% 2.44/0.98  gc_basic_clause_elim:                   0
% 2.44/0.98  forced_gc_time:                         0
% 2.44/0.98  parsing_time:                           0.013
% 2.44/0.98  unif_index_cands_time:                  0.
% 2.44/0.98  unif_index_add_time:                    0.
% 2.44/0.98  orderings_time:                         0.
% 2.44/0.98  out_proof_time:                         0.011
% 2.44/0.98  total_time:                             0.111
% 2.44/0.98  num_of_symbols:                         61
% 2.44/0.98  num_of_terms:                           3104
% 2.44/0.98  
% 2.44/0.98  ------ Preprocessing
% 2.44/0.98  
% 2.44/0.98  num_of_splits:                          0
% 2.44/0.98  num_of_split_atoms:                     0
% 2.44/0.98  num_of_reused_defs:                     0
% 2.44/0.98  num_eq_ax_congr_red:                    24
% 2.44/0.98  num_of_sem_filtered_clauses:            1
% 2.44/0.98  num_of_subtypes:                        0
% 2.44/0.98  monotx_restored_types:                  0
% 2.44/0.98  sat_num_of_epr_types:                   0
% 2.44/0.98  sat_num_of_non_cyclic_types:            0
% 2.44/0.98  sat_guarded_non_collapsed_types:        0
% 2.44/0.98  num_pure_diseq_elim:                    0
% 2.44/0.98  simp_replaced_by:                       0
% 2.44/0.98  res_preprocessed:                       153
% 2.44/0.98  prep_upred:                             0
% 2.44/0.98  prep_unflattend:                        84
% 2.44/0.98  smt_new_axioms:                         0
% 2.44/0.98  pred_elim_cands:                        4
% 2.44/0.98  pred_elim:                              7
% 2.44/0.98  pred_elim_cl:                           8
% 2.44/0.98  pred_elim_cycles:                       13
% 2.44/0.98  merged_defs:                            14
% 2.44/0.98  merged_defs_ncl:                        0
% 2.44/0.98  bin_hyper_res:                          14
% 2.44/0.98  prep_cycles:                            4
% 2.44/0.98  pred_elim_time:                         0.015
% 2.44/0.98  splitting_time:                         0.
% 2.44/0.98  sem_filter_time:                        0.
% 2.44/0.98  monotx_time:                            0.
% 2.44/0.98  subtype_inf_time:                       0.
% 2.44/0.98  
% 2.44/0.98  ------ Problem properties
% 2.44/0.98  
% 2.44/0.98  clauses:                                28
% 2.44/0.98  conjectures:                            1
% 2.44/0.98  epr:                                    3
% 2.44/0.98  horn:                                   20
% 2.44/0.98  ground:                                 4
% 2.44/0.98  unary:                                  11
% 2.44/0.98  binary:                                 8
% 2.44/0.98  lits:                                   56
% 2.44/0.98  lits_eq:                                16
% 2.44/0.98  fd_pure:                                0
% 2.44/0.98  fd_pseudo:                              0
% 2.44/0.98  fd_cond:                                4
% 2.44/0.98  fd_pseudo_cond:                         3
% 2.44/0.98  ac_symbols:                             0
% 2.44/0.98  
% 2.44/0.98  ------ Propositional Solver
% 2.44/0.98  
% 2.44/0.98  prop_solver_calls:                      26
% 2.44/0.98  prop_fast_solver_calls:                 1029
% 2.44/0.98  smt_solver_calls:                       0
% 2.44/0.98  smt_fast_solver_calls:                  0
% 2.44/0.98  prop_num_of_clauses:                    1062
% 2.44/0.98  prop_preprocess_simplified:             5249
% 2.44/0.98  prop_fo_subsumed:                       26
% 2.44/0.98  prop_solver_time:                       0.
% 2.44/0.98  smt_solver_time:                        0.
% 2.44/0.98  smt_fast_solver_time:                   0.
% 2.44/0.98  prop_fast_solver_time:                  0.
% 2.44/0.98  prop_unsat_core_time:                   0.
% 2.44/0.98  
% 2.44/0.98  ------ QBF
% 2.44/0.98  
% 2.44/0.98  qbf_q_res:                              0
% 2.44/0.98  qbf_num_tautologies:                    0
% 2.44/0.98  qbf_prep_cycles:                        0
% 2.44/0.98  
% 2.44/0.98  ------ BMC1
% 2.44/0.98  
% 2.44/0.98  bmc1_current_bound:                     -1
% 2.44/0.98  bmc1_last_solved_bound:                 -1
% 2.44/0.98  bmc1_unsat_core_size:                   -1
% 2.44/0.98  bmc1_unsat_core_parents_size:           -1
% 2.44/0.98  bmc1_merge_next_fun:                    0
% 2.44/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.44/0.98  
% 2.44/0.98  ------ Instantiation
% 2.44/0.98  
% 2.44/0.98  inst_num_of_clauses:                    307
% 2.44/0.98  inst_num_in_passive:                    41
% 2.44/0.98  inst_num_in_active:                     163
% 2.44/0.98  inst_num_in_unprocessed:                103
% 2.44/0.98  inst_num_of_loops:                      180
% 2.44/0.98  inst_num_of_learning_restarts:          0
% 2.44/0.98  inst_num_moves_active_passive:          15
% 2.44/0.98  inst_lit_activity:                      0
% 2.44/0.98  inst_lit_activity_moves:                0
% 2.44/0.98  inst_num_tautologies:                   0
% 2.44/0.98  inst_num_prop_implied:                  0
% 2.44/0.98  inst_num_existing_simplified:           0
% 2.44/0.98  inst_num_eq_res_simplified:             0
% 2.44/0.98  inst_num_child_elim:                    0
% 2.44/0.98  inst_num_of_dismatching_blockings:      77
% 2.44/0.98  inst_num_of_non_proper_insts:           172
% 2.44/0.98  inst_num_of_duplicates:                 0
% 2.44/0.98  inst_inst_num_from_inst_to_res:         0
% 2.44/0.98  inst_dismatching_checking_time:         0.
% 2.44/0.98  
% 2.44/0.98  ------ Resolution
% 2.44/0.98  
% 2.44/0.98  res_num_of_clauses:                     0
% 2.44/0.98  res_num_in_passive:                     0
% 2.44/0.98  res_num_in_active:                      0
% 2.44/0.98  res_num_of_loops:                       157
% 2.44/0.98  res_forward_subset_subsumed:            13
% 2.44/0.98  res_backward_subset_subsumed:           0
% 2.44/0.98  res_forward_subsumed:                   4
% 2.44/0.98  res_backward_subsumed:                  0
% 2.44/0.98  res_forward_subsumption_resolution:     0
% 2.44/0.98  res_backward_subsumption_resolution:    0
% 2.44/0.98  res_clause_to_clause_subsumption:       78
% 2.44/0.98  res_orphan_elimination:                 0
% 2.44/0.98  res_tautology_del:                      45
% 2.44/0.98  res_num_eq_res_simplified:              6
% 2.44/0.98  res_num_sel_changes:                    0
% 2.44/0.98  res_moves_from_active_to_pass:          0
% 2.44/0.98  
% 2.44/0.98  ------ Superposition
% 2.44/0.98  
% 2.44/0.98  sup_time_total:                         0.
% 2.44/0.98  sup_time_generating:                    0.
% 2.44/0.98  sup_time_sim_full:                      0.
% 2.44/0.98  sup_time_sim_immed:                     0.
% 2.44/0.98  
% 2.44/0.98  sup_num_of_clauses:                     50
% 2.44/0.98  sup_num_in_active:                      33
% 2.44/0.98  sup_num_in_passive:                     17
% 2.44/0.98  sup_num_of_loops:                       35
% 2.44/0.98  sup_fw_superposition:                   28
% 2.44/0.98  sup_bw_superposition:                   8
% 2.44/0.98  sup_immediate_simplified:               2
% 2.44/0.98  sup_given_eliminated:                   0
% 2.44/0.98  comparisons_done:                       0
% 2.44/0.98  comparisons_avoided:                    3
% 2.44/0.98  
% 2.44/0.98  ------ Simplifications
% 2.44/0.98  
% 2.44/0.98  
% 2.44/0.98  sim_fw_subset_subsumed:                 0
% 2.44/0.98  sim_bw_subset_subsumed:                 0
% 2.44/0.98  sim_fw_subsumed:                        2
% 2.44/0.98  sim_bw_subsumed:                        0
% 2.44/0.98  sim_fw_subsumption_res:                 0
% 2.44/0.98  sim_bw_subsumption_res:                 0
% 2.44/0.98  sim_tautology_del:                      2
% 2.44/0.98  sim_eq_tautology_del:                   6
% 2.44/0.98  sim_eq_res_simp:                        0
% 2.44/0.98  sim_fw_demodulated:                     1
% 2.44/0.98  sim_bw_demodulated:                     3
% 2.44/0.98  sim_light_normalised:                   0
% 2.44/0.98  sim_joinable_taut:                      0
% 2.44/0.98  sim_joinable_simp:                      0
% 2.44/0.98  sim_ac_normalised:                      0
% 2.44/0.98  sim_smt_subsumption:                    0
% 2.44/0.98  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:52 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 347 expanded)
%              Number of clauses        :   74 ( 103 expanded)
%              Number of leaves         :   20 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :  511 (2017 expanded)
%              Number of equality atoms :   91 ( 106 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f66,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f90,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f23,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( r1_tsep_1(X2,X1)
            | r1_tsep_1(X1,X2) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( r1_tsep_1(sK7,X1)
          | r1_tsep_1(X1,sK7) )
        & m1_pre_topc(X1,sK7)
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( r1_tsep_1(X2,sK6)
              | r1_tsep_1(sK6,X2) )
            & m1_pre_topc(sK6,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK5)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ( r1_tsep_1(sK7,sK6)
      | r1_tsep_1(sK6,sK7) )
    & m1_pre_topc(sK6,sK7)
    & m1_pre_topc(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f40,f63,f62,f61])).

fof(f101,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f97,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f107,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f89,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,
    ( r1_tsep_1(sK7,sK6)
    | r1_tsep_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f49])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f106,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2149,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_593,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_594,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_596,plain,
    ( l1_pre_topc(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_37])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_30,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_494,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r2_hidden(X2,X3)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X3)
    | u1_struct_0(X0) != X2
    | k1_zfmisc_1(u1_struct_0(X1)) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_495,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r2_hidden(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_556,plain,
    ( r2_hidden(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
    | sK6 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_495,c_32])).

cnf(c_557,plain,
    ( r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_603,plain,
    ( r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK7)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_596,c_557])).

cnf(c_2122,plain,
    ( r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_20,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2130,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3231,plain,
    ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_2130])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2145,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5325,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3231,c_2145])).

cnf(c_5793,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK7)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2149,c_5325])).

cnf(c_40,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_41,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_26,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_57,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_59,plain,
    ( v2_struct_0(sK6) = iProver_top
    | l1_struct_0(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_24,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_61,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_63,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_struct_0(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_569,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_570,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_571,plain,
    ( l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_595,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_651,plain,
    ( l1_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_596])).

cnf(c_652,plain,
    ( l1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_653,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_604,plain,
    ( l1_pre_topc(sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_596,c_570])).

cnf(c_644,plain,
    ( l1_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_604])).

cnf(c_645,plain,
    ( l1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_527,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_528,plain,
    ( ~ l1_struct_0(sK6)
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_663,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_645,c_528])).

cnf(c_682,plain,
    ( r2_hidden(sK0(X0),X0)
    | u1_struct_0(sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_663])).

cnf(c_683,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_684,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_28,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2375,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2376,plain,
    ( r1_tsep_1(sK6,sK7) != iProver_top
    | r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2375])).

cnf(c_29,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2577,plain,
    ( r1_tsep_1(sK6,sK7)
    | ~ r1_tsep_1(sK7,sK6)
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2578,plain,
    ( r1_tsep_1(sK6,sK7) = iProver_top
    | r1_tsep_1(sK7,sK6) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2577])).

cnf(c_31,negated_conjecture,
    ( r1_tsep_1(sK6,sK7)
    | r1_tsep_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2124,plain,
    ( r1_tsep_1(sK6,sK7) = iProver_top
    | r1_tsep_1(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2125,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3114,plain,
    ( r1_tsep_1(sK7,sK6) = iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2124,c_2125])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2569,plain,
    ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2868,plain,
    ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0))
    | ~ r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_2569])).

cnf(c_4046,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_4047,plain,
    ( r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4046])).

cnf(c_8834,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5793,c_40,c_41,c_59,c_63,c_571,c_595,c_653,c_684,c_2376,c_2578,c_3114,c_4047])).

cnf(c_13,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2137,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2131,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2148,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3335,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_2148])).

cnf(c_9781,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_3335])).

cnf(c_10050,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_8834,c_9781])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:55:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/0.98  
% 3.00/0.98  ------  iProver source info
% 3.00/0.98  
% 3.00/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.00/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/0.98  git: non_committed_changes: false
% 3.00/0.98  git: last_make_outside_of_git: false
% 3.00/0.98  
% 3.00/0.98  ------ 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options
% 3.00/0.98  
% 3.00/0.98  --out_options                           all
% 3.00/0.98  --tptp_safe_out                         true
% 3.00/0.98  --problem_path                          ""
% 3.00/0.98  --include_path                          ""
% 3.00/0.98  --clausifier                            res/vclausify_rel
% 3.00/0.98  --clausifier_options                    --mode clausify
% 3.00/0.98  --stdin                                 false
% 3.00/0.98  --stats_out                             all
% 3.00/0.98  
% 3.00/0.98  ------ General Options
% 3.00/0.98  
% 3.00/0.98  --fof                                   false
% 3.00/0.98  --time_out_real                         305.
% 3.00/0.98  --time_out_virtual                      -1.
% 3.00/0.98  --symbol_type_check                     false
% 3.00/0.98  --clausify_out                          false
% 3.00/0.98  --sig_cnt_out                           false
% 3.00/0.98  --trig_cnt_out                          false
% 3.00/0.98  --trig_cnt_out_tolerance                1.
% 3.00/0.98  --trig_cnt_out_sk_spl                   false
% 3.00/0.98  --abstr_cl_out                          false
% 3.00/0.98  
% 3.00/0.98  ------ Global Options
% 3.00/0.98  
% 3.00/0.98  --schedule                              default
% 3.00/0.98  --add_important_lit                     false
% 3.00/0.98  --prop_solver_per_cl                    1000
% 3.00/0.98  --min_unsat_core                        false
% 3.00/0.98  --soft_assumptions                      false
% 3.00/0.98  --soft_lemma_size                       3
% 3.00/0.98  --prop_impl_unit_size                   0
% 3.00/0.98  --prop_impl_unit                        []
% 3.00/0.98  --share_sel_clauses                     true
% 3.00/0.98  --reset_solvers                         false
% 3.00/0.98  --bc_imp_inh                            [conj_cone]
% 3.00/0.98  --conj_cone_tolerance                   3.
% 3.00/0.98  --extra_neg_conj                        none
% 3.00/0.98  --large_theory_mode                     true
% 3.00/0.98  --prolific_symb_bound                   200
% 3.00/0.98  --lt_threshold                          2000
% 3.00/0.98  --clause_weak_htbl                      true
% 3.00/0.98  --gc_record_bc_elim                     false
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing Options
% 3.00/0.98  
% 3.00/0.98  --preprocessing_flag                    true
% 3.00/0.98  --time_out_prep_mult                    0.1
% 3.00/0.98  --splitting_mode                        input
% 3.00/0.98  --splitting_grd                         true
% 3.00/0.98  --splitting_cvd                         false
% 3.00/0.98  --splitting_cvd_svl                     false
% 3.00/0.98  --splitting_nvd                         32
% 3.00/0.98  --sub_typing                            true
% 3.00/0.98  --prep_gs_sim                           true
% 3.00/0.98  --prep_unflatten                        true
% 3.00/0.98  --prep_res_sim                          true
% 3.00/0.98  --prep_upred                            true
% 3.00/0.98  --prep_sem_filter                       exhaustive
% 3.00/0.98  --prep_sem_filter_out                   false
% 3.00/0.98  --pred_elim                             true
% 3.00/0.98  --res_sim_input                         true
% 3.00/0.98  --eq_ax_congr_red                       true
% 3.00/0.98  --pure_diseq_elim                       true
% 3.00/0.98  --brand_transform                       false
% 3.00/0.98  --non_eq_to_eq                          false
% 3.00/0.98  --prep_def_merge                        true
% 3.00/0.98  --prep_def_merge_prop_impl              false
% 3.00/0.98  --prep_def_merge_mbd                    true
% 3.00/0.98  --prep_def_merge_tr_red                 false
% 3.00/0.98  --prep_def_merge_tr_cl                  false
% 3.00/0.98  --smt_preprocessing                     true
% 3.00/0.98  --smt_ac_axioms                         fast
% 3.00/0.98  --preprocessed_out                      false
% 3.00/0.98  --preprocessed_stats                    false
% 3.00/0.98  
% 3.00/0.98  ------ Abstraction refinement Options
% 3.00/0.98  
% 3.00/0.98  --abstr_ref                             []
% 3.00/0.98  --abstr_ref_prep                        false
% 3.00/0.98  --abstr_ref_until_sat                   false
% 3.00/0.98  --abstr_ref_sig_restrict                funpre
% 3.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.98  --abstr_ref_under                       []
% 3.00/0.98  
% 3.00/0.98  ------ SAT Options
% 3.00/0.98  
% 3.00/0.98  --sat_mode                              false
% 3.00/0.98  --sat_fm_restart_options                ""
% 3.00/0.98  --sat_gr_def                            false
% 3.00/0.98  --sat_epr_types                         true
% 3.00/0.98  --sat_non_cyclic_types                  false
% 3.00/0.98  --sat_finite_models                     false
% 3.00/0.98  --sat_fm_lemmas                         false
% 3.00/0.98  --sat_fm_prep                           false
% 3.00/0.98  --sat_fm_uc_incr                        true
% 3.00/0.98  --sat_out_model                         small
% 3.00/0.98  --sat_out_clauses                       false
% 3.00/0.98  
% 3.00/0.98  ------ QBF Options
% 3.00/0.98  
% 3.00/0.98  --qbf_mode                              false
% 3.00/0.98  --qbf_elim_univ                         false
% 3.00/0.98  --qbf_dom_inst                          none
% 3.00/0.98  --qbf_dom_pre_inst                      false
% 3.00/0.98  --qbf_sk_in                             false
% 3.00/0.98  --qbf_pred_elim                         true
% 3.00/0.98  --qbf_split                             512
% 3.00/0.98  
% 3.00/0.98  ------ BMC1 Options
% 3.00/0.98  
% 3.00/0.98  --bmc1_incremental                      false
% 3.00/0.98  --bmc1_axioms                           reachable_all
% 3.00/0.98  --bmc1_min_bound                        0
% 3.00/0.98  --bmc1_max_bound                        -1
% 3.00/0.98  --bmc1_max_bound_default                -1
% 3.00/0.98  --bmc1_symbol_reachability              true
% 3.00/0.98  --bmc1_property_lemmas                  false
% 3.00/0.98  --bmc1_k_induction                      false
% 3.00/0.98  --bmc1_non_equiv_states                 false
% 3.00/0.98  --bmc1_deadlock                         false
% 3.00/0.98  --bmc1_ucm                              false
% 3.00/0.98  --bmc1_add_unsat_core                   none
% 3.00/0.98  --bmc1_unsat_core_children              false
% 3.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.98  --bmc1_out_stat                         full
% 3.00/0.98  --bmc1_ground_init                      false
% 3.00/0.98  --bmc1_pre_inst_next_state              false
% 3.00/0.98  --bmc1_pre_inst_state                   false
% 3.00/0.98  --bmc1_pre_inst_reach_state             false
% 3.00/0.98  --bmc1_out_unsat_core                   false
% 3.00/0.98  --bmc1_aig_witness_out                  false
% 3.00/0.98  --bmc1_verbose                          false
% 3.00/0.98  --bmc1_dump_clauses_tptp                false
% 3.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.98  --bmc1_dump_file                        -
% 3.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.98  --bmc1_ucm_extend_mode                  1
% 3.00/0.98  --bmc1_ucm_init_mode                    2
% 3.00/0.98  --bmc1_ucm_cone_mode                    none
% 3.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.98  --bmc1_ucm_relax_model                  4
% 3.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.98  --bmc1_ucm_layered_model                none
% 3.00/0.98  --bmc1_ucm_max_lemma_size               10
% 3.00/0.98  
% 3.00/0.98  ------ AIG Options
% 3.00/0.98  
% 3.00/0.98  --aig_mode                              false
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation Options
% 3.00/0.98  
% 3.00/0.98  --instantiation_flag                    true
% 3.00/0.98  --inst_sos_flag                         false
% 3.00/0.98  --inst_sos_phase                        true
% 3.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel_side                     num_symb
% 3.00/0.98  --inst_solver_per_active                1400
% 3.00/0.98  --inst_solver_calls_frac                1.
% 3.00/0.98  --inst_passive_queue_type               priority_queues
% 3.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.98  --inst_passive_queues_freq              [25;2]
% 3.00/0.98  --inst_dismatching                      true
% 3.00/0.98  --inst_eager_unprocessed_to_passive     true
% 3.00/0.98  --inst_prop_sim_given                   true
% 3.00/0.98  --inst_prop_sim_new                     false
% 3.00/0.98  --inst_subs_new                         false
% 3.00/0.98  --inst_eq_res_simp                      false
% 3.00/0.98  --inst_subs_given                       false
% 3.00/0.98  --inst_orphan_elimination               true
% 3.00/0.98  --inst_learning_loop_flag               true
% 3.00/0.98  --inst_learning_start                   3000
% 3.00/0.98  --inst_learning_factor                  2
% 3.00/0.98  --inst_start_prop_sim_after_learn       3
% 3.00/0.98  --inst_sel_renew                        solver
% 3.00/0.98  --inst_lit_activity_flag                true
% 3.00/0.98  --inst_restr_to_given                   false
% 3.00/0.98  --inst_activity_threshold               500
% 3.00/0.98  --inst_out_proof                        true
% 3.00/0.98  
% 3.00/0.98  ------ Resolution Options
% 3.00/0.98  
% 3.00/0.98  --resolution_flag                       true
% 3.00/0.98  --res_lit_sel                           adaptive
% 3.00/0.98  --res_lit_sel_side                      none
% 3.00/0.98  --res_ordering                          kbo
% 3.00/0.98  --res_to_prop_solver                    active
% 3.00/0.98  --res_prop_simpl_new                    false
% 3.00/0.98  --res_prop_simpl_given                  true
% 3.00/0.98  --res_passive_queue_type                priority_queues
% 3.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.98  --res_passive_queues_freq               [15;5]
% 3.00/0.98  --res_forward_subs                      full
% 3.00/0.98  --res_backward_subs                     full
% 3.00/0.98  --res_forward_subs_resolution           true
% 3.00/0.98  --res_backward_subs_resolution          true
% 3.00/0.98  --res_orphan_elimination                true
% 3.00/0.98  --res_time_limit                        2.
% 3.00/0.98  --res_out_proof                         true
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Options
% 3.00/0.98  
% 3.00/0.98  --superposition_flag                    true
% 3.00/0.98  --sup_passive_queue_type                priority_queues
% 3.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.98  --demod_completeness_check              fast
% 3.00/0.98  --demod_use_ground                      true
% 3.00/0.98  --sup_to_prop_solver                    passive
% 3.00/0.98  --sup_prop_simpl_new                    true
% 3.00/0.98  --sup_prop_simpl_given                  true
% 3.00/0.98  --sup_fun_splitting                     false
% 3.00/0.98  --sup_smt_interval                      50000
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Simplification Setup
% 3.00/0.98  
% 3.00/0.98  --sup_indices_passive                   []
% 3.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_full_bw                           [BwDemod]
% 3.00/0.98  --sup_immed_triv                        [TrivRules]
% 3.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_immed_bw_main                     []
% 3.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  
% 3.00/0.98  ------ Combination Options
% 3.00/0.98  
% 3.00/0.98  --comb_res_mult                         3
% 3.00/0.98  --comb_sup_mult                         2
% 3.00/0.98  --comb_inst_mult                        10
% 3.00/0.98  
% 3.00/0.98  ------ Debug Options
% 3.00/0.98  
% 3.00/0.98  --dbg_backtrace                         false
% 3.00/0.98  --dbg_dump_prop_clauses                 false
% 3.00/0.98  --dbg_dump_prop_clauses_file            -
% 3.00/0.98  --dbg_out_stat                          false
% 3.00/0.98  ------ Parsing...
% 3.00/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/0.98  ------ Proving...
% 3.00/0.98  ------ Problem Properties 
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  clauses                                 35
% 3.00/0.98  conjectures                             1
% 3.00/0.98  EPR                                     13
% 3.00/0.98  Horn                                    25
% 3.00/0.98  unary                                   9
% 3.00/0.98  binary                                  18
% 3.00/0.98  lits                                    72
% 3.00/0.98  lits eq                                 4
% 3.00/0.98  fd_pure                                 0
% 3.00/0.98  fd_pseudo                               0
% 3.00/0.98  fd_cond                                 0
% 3.00/0.98  fd_pseudo_cond                          3
% 3.00/0.98  AC symbols                              0
% 3.00/0.98  
% 3.00/0.98  ------ Schedule dynamic 5 is on 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  ------ 
% 3.00/0.98  Current options:
% 3.00/0.98  ------ 
% 3.00/0.98  
% 3.00/0.98  ------ Input Options
% 3.00/0.98  
% 3.00/0.98  --out_options                           all
% 3.00/0.98  --tptp_safe_out                         true
% 3.00/0.98  --problem_path                          ""
% 3.00/0.98  --include_path                          ""
% 3.00/0.98  --clausifier                            res/vclausify_rel
% 3.00/0.98  --clausifier_options                    --mode clausify
% 3.00/0.98  --stdin                                 false
% 3.00/0.98  --stats_out                             all
% 3.00/0.98  
% 3.00/0.98  ------ General Options
% 3.00/0.98  
% 3.00/0.98  --fof                                   false
% 3.00/0.98  --time_out_real                         305.
% 3.00/0.98  --time_out_virtual                      -1.
% 3.00/0.98  --symbol_type_check                     false
% 3.00/0.98  --clausify_out                          false
% 3.00/0.98  --sig_cnt_out                           false
% 3.00/0.98  --trig_cnt_out                          false
% 3.00/0.98  --trig_cnt_out_tolerance                1.
% 3.00/0.98  --trig_cnt_out_sk_spl                   false
% 3.00/0.98  --abstr_cl_out                          false
% 3.00/0.98  
% 3.00/0.98  ------ Global Options
% 3.00/0.98  
% 3.00/0.98  --schedule                              default
% 3.00/0.98  --add_important_lit                     false
% 3.00/0.98  --prop_solver_per_cl                    1000
% 3.00/0.98  --min_unsat_core                        false
% 3.00/0.98  --soft_assumptions                      false
% 3.00/0.98  --soft_lemma_size                       3
% 3.00/0.98  --prop_impl_unit_size                   0
% 3.00/0.98  --prop_impl_unit                        []
% 3.00/0.98  --share_sel_clauses                     true
% 3.00/0.98  --reset_solvers                         false
% 3.00/0.98  --bc_imp_inh                            [conj_cone]
% 3.00/0.98  --conj_cone_tolerance                   3.
% 3.00/0.98  --extra_neg_conj                        none
% 3.00/0.98  --large_theory_mode                     true
% 3.00/0.98  --prolific_symb_bound                   200
% 3.00/0.98  --lt_threshold                          2000
% 3.00/0.98  --clause_weak_htbl                      true
% 3.00/0.98  --gc_record_bc_elim                     false
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing Options
% 3.00/0.98  
% 3.00/0.98  --preprocessing_flag                    true
% 3.00/0.98  --time_out_prep_mult                    0.1
% 3.00/0.98  --splitting_mode                        input
% 3.00/0.98  --splitting_grd                         true
% 3.00/0.98  --splitting_cvd                         false
% 3.00/0.98  --splitting_cvd_svl                     false
% 3.00/0.98  --splitting_nvd                         32
% 3.00/0.98  --sub_typing                            true
% 3.00/0.98  --prep_gs_sim                           true
% 3.00/0.98  --prep_unflatten                        true
% 3.00/0.98  --prep_res_sim                          true
% 3.00/0.98  --prep_upred                            true
% 3.00/0.98  --prep_sem_filter                       exhaustive
% 3.00/0.98  --prep_sem_filter_out                   false
% 3.00/0.98  --pred_elim                             true
% 3.00/0.98  --res_sim_input                         true
% 3.00/0.98  --eq_ax_congr_red                       true
% 3.00/0.98  --pure_diseq_elim                       true
% 3.00/0.98  --brand_transform                       false
% 3.00/0.98  --non_eq_to_eq                          false
% 3.00/0.98  --prep_def_merge                        true
% 3.00/0.98  --prep_def_merge_prop_impl              false
% 3.00/0.98  --prep_def_merge_mbd                    true
% 3.00/0.98  --prep_def_merge_tr_red                 false
% 3.00/0.98  --prep_def_merge_tr_cl                  false
% 3.00/0.98  --smt_preprocessing                     true
% 3.00/0.98  --smt_ac_axioms                         fast
% 3.00/0.98  --preprocessed_out                      false
% 3.00/0.98  --preprocessed_stats                    false
% 3.00/0.98  
% 3.00/0.98  ------ Abstraction refinement Options
% 3.00/0.98  
% 3.00/0.98  --abstr_ref                             []
% 3.00/0.98  --abstr_ref_prep                        false
% 3.00/0.98  --abstr_ref_until_sat                   false
% 3.00/0.98  --abstr_ref_sig_restrict                funpre
% 3.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.98  --abstr_ref_under                       []
% 3.00/0.98  
% 3.00/0.98  ------ SAT Options
% 3.00/0.98  
% 3.00/0.98  --sat_mode                              false
% 3.00/0.98  --sat_fm_restart_options                ""
% 3.00/0.98  --sat_gr_def                            false
% 3.00/0.98  --sat_epr_types                         true
% 3.00/0.98  --sat_non_cyclic_types                  false
% 3.00/0.98  --sat_finite_models                     false
% 3.00/0.98  --sat_fm_lemmas                         false
% 3.00/0.98  --sat_fm_prep                           false
% 3.00/0.98  --sat_fm_uc_incr                        true
% 3.00/0.98  --sat_out_model                         small
% 3.00/0.98  --sat_out_clauses                       false
% 3.00/0.98  
% 3.00/0.98  ------ QBF Options
% 3.00/0.98  
% 3.00/0.98  --qbf_mode                              false
% 3.00/0.98  --qbf_elim_univ                         false
% 3.00/0.98  --qbf_dom_inst                          none
% 3.00/0.98  --qbf_dom_pre_inst                      false
% 3.00/0.98  --qbf_sk_in                             false
% 3.00/0.98  --qbf_pred_elim                         true
% 3.00/0.98  --qbf_split                             512
% 3.00/0.98  
% 3.00/0.98  ------ BMC1 Options
% 3.00/0.98  
% 3.00/0.98  --bmc1_incremental                      false
% 3.00/0.98  --bmc1_axioms                           reachable_all
% 3.00/0.98  --bmc1_min_bound                        0
% 3.00/0.98  --bmc1_max_bound                        -1
% 3.00/0.98  --bmc1_max_bound_default                -1
% 3.00/0.98  --bmc1_symbol_reachability              true
% 3.00/0.98  --bmc1_property_lemmas                  false
% 3.00/0.98  --bmc1_k_induction                      false
% 3.00/0.98  --bmc1_non_equiv_states                 false
% 3.00/0.98  --bmc1_deadlock                         false
% 3.00/0.98  --bmc1_ucm                              false
% 3.00/0.98  --bmc1_add_unsat_core                   none
% 3.00/0.98  --bmc1_unsat_core_children              false
% 3.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.98  --bmc1_out_stat                         full
% 3.00/0.98  --bmc1_ground_init                      false
% 3.00/0.98  --bmc1_pre_inst_next_state              false
% 3.00/0.98  --bmc1_pre_inst_state                   false
% 3.00/0.98  --bmc1_pre_inst_reach_state             false
% 3.00/0.98  --bmc1_out_unsat_core                   false
% 3.00/0.98  --bmc1_aig_witness_out                  false
% 3.00/0.98  --bmc1_verbose                          false
% 3.00/0.98  --bmc1_dump_clauses_tptp                false
% 3.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.98  --bmc1_dump_file                        -
% 3.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.98  --bmc1_ucm_extend_mode                  1
% 3.00/0.98  --bmc1_ucm_init_mode                    2
% 3.00/0.98  --bmc1_ucm_cone_mode                    none
% 3.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.98  --bmc1_ucm_relax_model                  4
% 3.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.98  --bmc1_ucm_layered_model                none
% 3.00/0.98  --bmc1_ucm_max_lemma_size               10
% 3.00/0.98  
% 3.00/0.98  ------ AIG Options
% 3.00/0.98  
% 3.00/0.98  --aig_mode                              false
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation Options
% 3.00/0.98  
% 3.00/0.98  --instantiation_flag                    true
% 3.00/0.98  --inst_sos_flag                         false
% 3.00/0.98  --inst_sos_phase                        true
% 3.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.98  --inst_lit_sel_side                     none
% 3.00/0.98  --inst_solver_per_active                1400
% 3.00/0.98  --inst_solver_calls_frac                1.
% 3.00/0.98  --inst_passive_queue_type               priority_queues
% 3.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.98  --inst_passive_queues_freq              [25;2]
% 3.00/0.98  --inst_dismatching                      true
% 3.00/0.98  --inst_eager_unprocessed_to_passive     true
% 3.00/0.98  --inst_prop_sim_given                   true
% 3.00/0.98  --inst_prop_sim_new                     false
% 3.00/0.98  --inst_subs_new                         false
% 3.00/0.98  --inst_eq_res_simp                      false
% 3.00/0.98  --inst_subs_given                       false
% 3.00/0.98  --inst_orphan_elimination               true
% 3.00/0.98  --inst_learning_loop_flag               true
% 3.00/0.98  --inst_learning_start                   3000
% 3.00/0.98  --inst_learning_factor                  2
% 3.00/0.98  --inst_start_prop_sim_after_learn       3
% 3.00/0.98  --inst_sel_renew                        solver
% 3.00/0.98  --inst_lit_activity_flag                true
% 3.00/0.98  --inst_restr_to_given                   false
% 3.00/0.98  --inst_activity_threshold               500
% 3.00/0.98  --inst_out_proof                        true
% 3.00/0.98  
% 3.00/0.98  ------ Resolution Options
% 3.00/0.98  
% 3.00/0.98  --resolution_flag                       false
% 3.00/0.98  --res_lit_sel                           adaptive
% 3.00/0.98  --res_lit_sel_side                      none
% 3.00/0.98  --res_ordering                          kbo
% 3.00/0.98  --res_to_prop_solver                    active
% 3.00/0.98  --res_prop_simpl_new                    false
% 3.00/0.98  --res_prop_simpl_given                  true
% 3.00/0.98  --res_passive_queue_type                priority_queues
% 3.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.98  --res_passive_queues_freq               [15;5]
% 3.00/0.98  --res_forward_subs                      full
% 3.00/0.98  --res_backward_subs                     full
% 3.00/0.98  --res_forward_subs_resolution           true
% 3.00/0.98  --res_backward_subs_resolution          true
% 3.00/0.98  --res_orphan_elimination                true
% 3.00/0.98  --res_time_limit                        2.
% 3.00/0.98  --res_out_proof                         true
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Options
% 3.00/0.98  
% 3.00/0.98  --superposition_flag                    true
% 3.00/0.98  --sup_passive_queue_type                priority_queues
% 3.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.98  --demod_completeness_check              fast
% 3.00/0.98  --demod_use_ground                      true
% 3.00/0.98  --sup_to_prop_solver                    passive
% 3.00/0.98  --sup_prop_simpl_new                    true
% 3.00/0.98  --sup_prop_simpl_given                  true
% 3.00/0.98  --sup_fun_splitting                     false
% 3.00/0.98  --sup_smt_interval                      50000
% 3.00/0.98  
% 3.00/0.98  ------ Superposition Simplification Setup
% 3.00/0.98  
% 3.00/0.98  --sup_indices_passive                   []
% 3.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_full_bw                           [BwDemod]
% 3.00/0.98  --sup_immed_triv                        [TrivRules]
% 3.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_immed_bw_main                     []
% 3.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.98  
% 3.00/0.98  ------ Combination Options
% 3.00/0.98  
% 3.00/0.98  --comb_res_mult                         3
% 3.00/0.98  --comb_sup_mult                         2
% 3.00/0.98  --comb_inst_mult                        10
% 3.00/0.98  
% 3.00/0.98  ------ Debug Options
% 3.00/0.98  
% 3.00/0.98  --dbg_backtrace                         false
% 3.00/0.98  --dbg_dump_prop_clauses                 false
% 3.00/0.98  --dbg_dump_prop_clauses_file            -
% 3.00/0.98  --dbg_out_stat                          false
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  ------ Proving...
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  % SZS status Theorem for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98   Resolution empty clause
% 3.00/0.98  
% 3.00/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  fof(f1,axiom,(
% 3.00/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f41,plain,(
% 3.00/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.00/0.98    inference(nnf_transformation,[],[f1])).
% 3.00/0.98  
% 3.00/0.98  fof(f42,plain,(
% 3.00/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/0.98    inference(rectify,[],[f41])).
% 3.00/0.98  
% 3.00/0.98  fof(f43,plain,(
% 3.00/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f44,plain,(
% 3.00/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.00/0.98  
% 3.00/0.98  fof(f66,plain,(
% 3.00/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f44])).
% 3.00/0.98  
% 3.00/0.98  fof(f14,axiom,(
% 3.00/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f32,plain,(
% 3.00/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.00/0.98    inference(ennf_transformation,[],[f14])).
% 3.00/0.98  
% 3.00/0.98  fof(f90,plain,(
% 3.00/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f32])).
% 3.00/0.98  
% 3.00/0.98  fof(f19,conjecture,(
% 3.00/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f20,negated_conjecture,(
% 3.00/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 3.00/0.98    inference(negated_conjecture,[],[f19])).
% 3.00/0.98  
% 3.00/0.98  fof(f23,plain,(
% 3.00/0.98    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 3.00/0.98    inference(pure_predicate_removal,[],[f20])).
% 3.00/0.98  
% 3.00/0.98  fof(f39,plain,(
% 3.00/0.98    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f23])).
% 3.00/0.98  
% 3.00/0.98  fof(f40,plain,(
% 3.00/0.98    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.00/0.98    inference(flattening,[],[f39])).
% 3.00/0.98  
% 3.00/0.98  fof(f63,plain,(
% 3.00/0.98    ( ! [X0,X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((r1_tsep_1(sK7,X1) | r1_tsep_1(X1,sK7)) & m1_pre_topc(X1,sK7) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f62,plain,(
% 3.00/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((r1_tsep_1(X2,sK6) | r1_tsep_1(sK6,X2)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f61,plain,(
% 3.00/0.98    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f64,plain,(
% 3.00/0.98    (((r1_tsep_1(sK7,sK6) | r1_tsep_1(sK6,sK7)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 3.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f40,f63,f62,f61])).
% 3.00/0.98  
% 3.00/0.98  fof(f101,plain,(
% 3.00/0.98    m1_pre_topc(sK7,sK5)),
% 3.00/0.98    inference(cnf_transformation,[],[f64])).
% 3.00/0.98  
% 3.00/0.98  fof(f97,plain,(
% 3.00/0.98    l1_pre_topc(sK5)),
% 3.00/0.98    inference(cnf_transformation,[],[f64])).
% 3.00/0.98  
% 3.00/0.98  fof(f12,axiom,(
% 3.00/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f29,plain,(
% 3.00/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.00/0.98    inference(ennf_transformation,[],[f12])).
% 3.00/0.98  
% 3.00/0.98  fof(f30,plain,(
% 3.00/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.00/0.98    inference(flattening,[],[f29])).
% 3.00/0.98  
% 3.00/0.98  fof(f88,plain,(
% 3.00/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f30])).
% 3.00/0.98  
% 3.00/0.98  fof(f18,axiom,(
% 3.00/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f38,plain,(
% 3.00/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.00/0.98    inference(ennf_transformation,[],[f18])).
% 3.00/0.98  
% 3.00/0.98  fof(f95,plain,(
% 3.00/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f38])).
% 3.00/0.98  
% 3.00/0.98  fof(f102,plain,(
% 3.00/0.98    m1_pre_topc(sK6,sK7)),
% 3.00/0.98    inference(cnf_transformation,[],[f64])).
% 3.00/0.98  
% 3.00/0.98  fof(f10,axiom,(
% 3.00/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f55,plain,(
% 3.00/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.00/0.98    inference(nnf_transformation,[],[f10])).
% 3.00/0.98  
% 3.00/0.98  fof(f56,plain,(
% 3.00/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.00/0.98    inference(rectify,[],[f55])).
% 3.00/0.98  
% 3.00/0.98  fof(f57,plain,(
% 3.00/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f58,plain,(
% 3.00/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).
% 3.00/0.98  
% 3.00/0.98  fof(f82,plain,(
% 3.00/0.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.00/0.98    inference(cnf_transformation,[],[f58])).
% 3.00/0.98  
% 3.00/0.98  fof(f107,plain,(
% 3.00/0.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.00/0.98    inference(equality_resolution,[],[f82])).
% 3.00/0.98  
% 3.00/0.98  fof(f2,axiom,(
% 3.00/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f24,plain,(
% 3.00/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f2])).
% 3.00/0.98  
% 3.00/0.98  fof(f45,plain,(
% 3.00/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.00/0.98    inference(nnf_transformation,[],[f24])).
% 3.00/0.98  
% 3.00/0.98  fof(f46,plain,(
% 3.00/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.00/0.98    inference(rectify,[],[f45])).
% 3.00/0.98  
% 3.00/0.98  fof(f47,plain,(
% 3.00/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f48,plain,(
% 3.00/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 3.00/0.98  
% 3.00/0.98  fof(f67,plain,(
% 3.00/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f48])).
% 3.00/0.98  
% 3.00/0.98  fof(f98,plain,(
% 3.00/0.98    ~v2_struct_0(sK6)),
% 3.00/0.98    inference(cnf_transformation,[],[f64])).
% 3.00/0.98  
% 3.00/0.98  fof(f15,axiom,(
% 3.00/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f33,plain,(
% 3.00/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f15])).
% 3.00/0.98  
% 3.00/0.98  fof(f34,plain,(
% 3.00/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.00/0.98    inference(flattening,[],[f33])).
% 3.00/0.98  
% 3.00/0.98  fof(f91,plain,(
% 3.00/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f34])).
% 3.00/0.98  
% 3.00/0.98  fof(f13,axiom,(
% 3.00/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f31,plain,(
% 3.00/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.00/0.98    inference(ennf_transformation,[],[f13])).
% 3.00/0.98  
% 3.00/0.98  fof(f89,plain,(
% 3.00/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f31])).
% 3.00/0.98  
% 3.00/0.98  fof(f16,axiom,(
% 3.00/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f35,plain,(
% 3.00/0.98    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.00/0.98    inference(ennf_transformation,[],[f16])).
% 3.00/0.98  
% 3.00/0.98  fof(f60,plain,(
% 3.00/0.98    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.00/0.98    inference(nnf_transformation,[],[f35])).
% 3.00/0.98  
% 3.00/0.98  fof(f92,plain,(
% 3.00/0.98    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f60])).
% 3.00/0.98  
% 3.00/0.98  fof(f17,axiom,(
% 3.00/0.98    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f36,plain,(
% 3.00/0.98    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.00/0.98    inference(ennf_transformation,[],[f17])).
% 3.00/0.98  
% 3.00/0.98  fof(f37,plain,(
% 3.00/0.98    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.00/0.98    inference(flattening,[],[f36])).
% 3.00/0.98  
% 3.00/0.98  fof(f94,plain,(
% 3.00/0.98    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f37])).
% 3.00/0.98  
% 3.00/0.98  fof(f103,plain,(
% 3.00/0.98    r1_tsep_1(sK7,sK6) | r1_tsep_1(sK6,sK7)),
% 3.00/0.98    inference(cnf_transformation,[],[f64])).
% 3.00/0.98  
% 3.00/0.98  fof(f4,axiom,(
% 3.00/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f21,plain,(
% 3.00/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.00/0.98    inference(rectify,[],[f4])).
% 3.00/0.98  
% 3.00/0.98  fof(f26,plain,(
% 3.00/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.00/0.98    inference(ennf_transformation,[],[f21])).
% 3.00/0.98  
% 3.00/0.98  fof(f49,plain,(
% 3.00/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.00/0.98    introduced(choice_axiom,[])).
% 3.00/0.98  
% 3.00/0.98  fof(f50,plain,(
% 3.00/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f49])).
% 3.00/0.98  
% 3.00/0.98  fof(f73,plain,(
% 3.00/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f50])).
% 3.00/0.98  
% 3.00/0.98  fof(f6,axiom,(
% 3.00/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.98  
% 3.00/0.98  fof(f53,plain,(
% 3.00/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.98    inference(nnf_transformation,[],[f6])).
% 3.00/0.98  
% 3.00/0.98  fof(f54,plain,(
% 3.00/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.98    inference(flattening,[],[f53])).
% 3.00/0.98  
% 3.00/0.98  fof(f76,plain,(
% 3.00/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.00/0.98    inference(cnf_transformation,[],[f54])).
% 3.00/0.98  
% 3.00/0.98  fof(f105,plain,(
% 3.00/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.00/0.98    inference(equality_resolution,[],[f76])).
% 3.00/0.98  
% 3.00/0.98  fof(f83,plain,(
% 3.00/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.00/0.98    inference(cnf_transformation,[],[f58])).
% 3.00/0.98  
% 3.00/0.98  fof(f106,plain,(
% 3.00/0.98    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.00/0.98    inference(equality_resolution,[],[f83])).
% 3.00/0.98  
% 3.00/0.98  fof(f65,plain,(
% 3.00/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.00/0.98    inference(cnf_transformation,[],[f44])).
% 3.00/0.98  
% 3.00/0.98  cnf(c_0,plain,
% 3.00/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2149,plain,
% 3.00/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_25,plain,
% 3.00/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_33,negated_conjecture,
% 3.00/0.98      ( m1_pre_topc(sK7,sK5) ),
% 3.00/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_593,plain,
% 3.00/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK5 != X0 | sK7 != X1 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_594,plain,
% 3.00/0.98      ( ~ l1_pre_topc(sK5) | l1_pre_topc(sK7) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_593]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_37,negated_conjecture,
% 3.00/0.98      ( l1_pre_topc(sK5) ),
% 3.00/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_596,plain,
% 3.00/0.98      ( l1_pre_topc(sK7) ),
% 3.00/0.98      inference(global_propositional_subsumption,[status(thm)],[c_594,c_37]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_23,plain,
% 3.00/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_30,plain,
% 3.00/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.00/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.98      | ~ l1_pre_topc(X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_494,plain,
% 3.00/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.00/0.98      | r2_hidden(X2,X3)
% 3.00/0.98      | ~ l1_pre_topc(X1)
% 3.00/0.98      | v1_xboole_0(X3)
% 3.00/0.98      | u1_struct_0(X0) != X2
% 3.00/0.98      | k1_zfmisc_1(u1_struct_0(X1)) != X3 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_495,plain,
% 3.00/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.00/0.98      | r2_hidden(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.98      | ~ l1_pre_topc(X1)
% 3.00/0.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_494]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_32,negated_conjecture,
% 3.00/0.98      ( m1_pre_topc(sK6,sK7) ),
% 3.00/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_556,plain,
% 3.00/0.98      ( r2_hidden(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.98      | ~ l1_pre_topc(X1)
% 3.00/0.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/0.98      | sK6 != X0
% 3.00/0.98      | sK7 != X1 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_495,c_32]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_557,plain,
% 3.00/0.98      ( r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK7)))
% 3.00/0.98      | ~ l1_pre_topc(sK7)
% 3.00/0.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_556]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_603,plain,
% 3.00/0.98      ( r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK7)))
% 3.00/0.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) ),
% 3.00/0.98      inference(backward_subsumption_resolution,[status(thm)],[c_596,c_557]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2122,plain,
% 3.00/0.98      ( r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 3.00/0.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_20,plain,
% 3.00/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2130,plain,
% 3.00/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.00/0.98      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3231,plain,
% 3.00/0.98      ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top
% 3.00/0.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2122,c_2130]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4,plain,
% 3.00/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2145,plain,
% 3.00/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.00/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.00/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_5325,plain,
% 3.00/0.98      ( r2_hidden(X0,u1_struct_0(sK6)) != iProver_top
% 3.00/0.98      | r2_hidden(X0,u1_struct_0(sK7)) = iProver_top
% 3.00/0.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_3231,c_2145]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_5793,plain,
% 3.00/0.98      ( r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK7)) = iProver_top
% 3.00/0.98      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
% 3.00/0.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2149,c_5325]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_40,plain,
% 3.00/0.98      ( l1_pre_topc(sK5) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_36,negated_conjecture,
% 3.00/0.98      ( ~ v2_struct_0(sK6) ),
% 3.00/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_41,plain,
% 3.00/0.98      ( v2_struct_0(sK6) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_26,plain,
% 3.00/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_57,plain,
% 3.00/0.98      ( v2_struct_0(X0) = iProver_top
% 3.00/0.98      | l1_struct_0(X0) != iProver_top
% 3.00/0.98      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_59,plain,
% 3.00/0.98      ( v2_struct_0(sK6) = iProver_top
% 3.00/0.98      | l1_struct_0(sK6) != iProver_top
% 3.00/0.98      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_57]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_24,plain,
% 3.00/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_61,plain,
% 3.00/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_63,plain,
% 3.00/0.98      ( l1_pre_topc(sK6) != iProver_top | l1_struct_0(sK6) = iProver_top ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_61]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_569,plain,
% 3.00/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X1 | sK7 != X0 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_570,plain,
% 3.00/0.98      ( l1_pre_topc(sK6) | ~ l1_pre_topc(sK7) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_569]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_571,plain,
% 3.00/0.98      ( l1_pre_topc(sK6) = iProver_top | l1_pre_topc(sK7) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_595,plain,
% 3.00/0.98      ( l1_pre_topc(sK5) != iProver_top | l1_pre_topc(sK7) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_651,plain,
% 3.00/0.98      ( l1_struct_0(X0) | sK7 != X0 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_596]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_652,plain,
% 3.00/0.98      ( l1_struct_0(sK7) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_651]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_653,plain,
% 3.00/0.98      ( l1_struct_0(sK7) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_604,plain,
% 3.00/0.98      ( l1_pre_topc(sK6) ),
% 3.00/0.98      inference(backward_subsumption_resolution,[status(thm)],[c_596,c_570]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_644,plain,
% 3.00/0.98      ( l1_struct_0(X0) | sK6 != X0 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_604]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_645,plain,
% 3.00/0.98      ( l1_struct_0(sK6) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_644]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_527,plain,
% 3.00/0.98      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK6 != X0 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_36]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_528,plain,
% 3.00/0.98      ( ~ l1_struct_0(sK6) | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_527]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_663,plain,
% 3.00/0.98      ( ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 3.00/0.98      inference(backward_subsumption_resolution,[status(thm)],[c_645,c_528]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_682,plain,
% 3.00/0.98      ( r2_hidden(sK0(X0),X0) | u1_struct_0(sK6) != X0 ),
% 3.00/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_663]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_683,plain,
% 3.00/0.98      ( r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 3.00/0.98      inference(unflattening,[status(thm)],[c_682]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_684,plain,
% 3.00/0.98      ( r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_28,plain,
% 3.00/0.98      ( ~ r1_tsep_1(X0,X1)
% 3.00/0.98      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.00/0.98      | ~ l1_struct_0(X0)
% 3.00/0.98      | ~ l1_struct_0(X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2375,plain,
% 3.00/0.98      ( ~ r1_tsep_1(sK6,sK7)
% 3.00/0.98      | r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
% 3.00/0.98      | ~ l1_struct_0(sK6)
% 3.00/0.98      | ~ l1_struct_0(sK7) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_28]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2376,plain,
% 3.00/0.98      ( r1_tsep_1(sK6,sK7) != iProver_top
% 3.00/0.98      | r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top
% 3.00/0.98      | l1_struct_0(sK6) != iProver_top
% 3.00/0.98      | l1_struct_0(sK7) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_2375]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_29,plain,
% 3.00/0.98      ( ~ r1_tsep_1(X0,X1)
% 3.00/0.98      | r1_tsep_1(X1,X0)
% 3.00/0.98      | ~ l1_struct_0(X0)
% 3.00/0.98      | ~ l1_struct_0(X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2577,plain,
% 3.00/0.98      ( r1_tsep_1(sK6,sK7)
% 3.00/0.98      | ~ r1_tsep_1(sK7,sK6)
% 3.00/0.98      | ~ l1_struct_0(sK6)
% 3.00/0.98      | ~ l1_struct_0(sK7) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_29]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2578,plain,
% 3.00/0.98      ( r1_tsep_1(sK6,sK7) = iProver_top
% 3.00/0.98      | r1_tsep_1(sK7,sK6) != iProver_top
% 3.00/0.98      | l1_struct_0(sK6) != iProver_top
% 3.00/0.98      | l1_struct_0(sK7) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_2577]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_31,negated_conjecture,
% 3.00/0.98      ( r1_tsep_1(sK6,sK7) | r1_tsep_1(sK7,sK6) ),
% 3.00/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2124,plain,
% 3.00/0.98      ( r1_tsep_1(sK6,sK7) = iProver_top | r1_tsep_1(sK7,sK6) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2125,plain,
% 3.00/0.98      ( r1_tsep_1(X0,X1) != iProver_top
% 3.00/0.98      | r1_tsep_1(X1,X0) = iProver_top
% 3.00/0.98      | l1_struct_0(X0) != iProver_top
% 3.00/0.98      | l1_struct_0(X1) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3114,plain,
% 3.00/0.98      ( r1_tsep_1(sK7,sK6) = iProver_top
% 3.00/0.98      | l1_struct_0(sK6) != iProver_top
% 3.00/0.98      | l1_struct_0(sK7) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2124,c_2125]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_6,plain,
% 3.00/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2569,plain,
% 3.00/0.98      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.00/0.98      | ~ r2_hidden(X2,u1_struct_0(X0))
% 3.00/0.98      | ~ r2_hidden(X2,u1_struct_0(X1)) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2868,plain,
% 3.00/0.98      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.00/0.98      | ~ r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0))
% 3.00/0.98      | ~ r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X1)) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_2569]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4046,plain,
% 3.00/0.98      ( ~ r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
% 3.00/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6))
% 3.00/0.98      | ~ r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK7)) ),
% 3.00/0.98      inference(instantiation,[status(thm)],[c_2868]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_4047,plain,
% 3.00/0.98      ( r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 3.00/0.98      | r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 3.00/0.98      | r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK7)) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_4046]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_8834,plain,
% 3.00/0.98      ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 3.00/0.98      inference(global_propositional_subsumption,
% 3.00/0.98                [status(thm)],
% 3.00/0.98                [c_5793,c_40,c_41,c_59,c_63,c_571,c_595,c_653,c_684,c_2376,
% 3.00/0.98                 c_2578,c_3114,c_4047]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_13,plain,
% 3.00/0.98      ( r1_tarski(X0,X0) ),
% 3.00/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2137,plain,
% 3.00/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_19,plain,
% 3.00/0.98      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.00/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2131,plain,
% 3.00/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.00/0.98      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_1,plain,
% 3.00/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.00/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_2148,plain,
% 3.00/0.98      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_3335,plain,
% 3.00/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.00/0.98      | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2131,c_2148]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_9781,plain,
% 3.00/0.98      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_2137,c_3335]) ).
% 3.00/0.98  
% 3.00/0.98  cnf(c_10050,plain,
% 3.00/0.98      ( $false ),
% 3.00/0.98      inference(superposition,[status(thm)],[c_8834,c_9781]) ).
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/0.98  
% 3.00/0.98  ------                               Statistics
% 3.00/0.98  
% 3.00/0.98  ------ General
% 3.00/0.98  
% 3.00/0.98  abstr_ref_over_cycles:                  0
% 3.00/0.98  abstr_ref_under_cycles:                 0
% 3.00/0.98  gc_basic_clause_elim:                   0
% 3.00/0.98  forced_gc_time:                         0
% 3.00/0.98  parsing_time:                           0.009
% 3.00/0.98  unif_index_cands_time:                  0.
% 3.00/0.98  unif_index_add_time:                    0.
% 3.00/0.98  orderings_time:                         0.
% 3.00/0.98  out_proof_time:                         0.008
% 3.00/0.98  total_time:                             0.285
% 3.00/0.98  num_of_symbols:                         54
% 3.00/0.98  num_of_terms:                           8704
% 3.00/0.98  
% 3.00/0.98  ------ Preprocessing
% 3.00/0.98  
% 3.00/0.98  num_of_splits:                          0
% 3.00/0.98  num_of_split_atoms:                     0
% 3.00/0.98  num_of_reused_defs:                     0
% 3.00/0.98  num_eq_ax_congr_red:                    41
% 3.00/0.98  num_of_sem_filtered_clauses:            1
% 3.00/0.98  num_of_subtypes:                        0
% 3.00/0.98  monotx_restored_types:                  0
% 3.00/0.98  sat_num_of_epr_types:                   0
% 3.00/0.98  sat_num_of_non_cyclic_types:            0
% 3.00/0.98  sat_guarded_non_collapsed_types:        0
% 3.00/0.98  num_pure_diseq_elim:                    0
% 3.00/0.98  simp_replaced_by:                       0
% 3.00/0.98  res_preprocessed:                       164
% 3.00/0.98  prep_upred:                             0
% 3.00/0.98  prep_unflattend:                        34
% 3.00/0.98  smt_new_axioms:                         0
% 3.00/0.98  pred_elim_cands:                        6
% 3.00/0.98  pred_elim:                              4
% 3.00/0.98  pred_elim_cl:                           3
% 3.00/0.98  pred_elim_cycles:                       6
% 3.00/0.98  merged_defs:                            16
% 3.00/0.98  merged_defs_ncl:                        0
% 3.00/0.98  bin_hyper_res:                          16
% 3.00/0.98  prep_cycles:                            4
% 3.00/0.98  pred_elim_time:                         0.011
% 3.00/0.98  splitting_time:                         0.
% 3.00/0.98  sem_filter_time:                        0.
% 3.00/0.98  monotx_time:                            0.001
% 3.00/0.98  subtype_inf_time:                       0.
% 3.00/0.98  
% 3.00/0.98  ------ Problem properties
% 3.00/0.98  
% 3.00/0.98  clauses:                                35
% 3.00/0.98  conjectures:                            1
% 3.00/0.98  epr:                                    13
% 3.00/0.98  horn:                                   25
% 3.00/0.98  ground:                                 10
% 3.00/0.98  unary:                                  9
% 3.00/0.98  binary:                                 18
% 3.00/0.98  lits:                                   72
% 3.00/0.98  lits_eq:                                4
% 3.00/0.98  fd_pure:                                0
% 3.00/0.98  fd_pseudo:                              0
% 3.00/0.98  fd_cond:                                0
% 3.00/0.98  fd_pseudo_cond:                         3
% 3.00/0.98  ac_symbols:                             0
% 3.00/0.98  
% 3.00/0.98  ------ Propositional Solver
% 3.00/0.98  
% 3.00/0.98  prop_solver_calls:                      28
% 3.00/0.98  prop_fast_solver_calls:                 1060
% 3.00/0.98  smt_solver_calls:                       0
% 3.00/0.98  smt_fast_solver_calls:                  0
% 3.00/0.98  prop_num_of_clauses:                    3646
% 3.00/0.98  prop_preprocess_simplified:             10429
% 3.00/0.98  prop_fo_subsumed:                       33
% 3.00/0.98  prop_solver_time:                       0.
% 3.00/0.98  smt_solver_time:                        0.
% 3.00/0.98  smt_fast_solver_time:                   0.
% 3.00/0.98  prop_fast_solver_time:                  0.
% 3.00/0.98  prop_unsat_core_time:                   0.
% 3.00/0.98  
% 3.00/0.98  ------ QBF
% 3.00/0.98  
% 3.00/0.98  qbf_q_res:                              0
% 3.00/0.98  qbf_num_tautologies:                    0
% 3.00/0.98  qbf_prep_cycles:                        0
% 3.00/0.98  
% 3.00/0.98  ------ BMC1
% 3.00/0.98  
% 3.00/0.98  bmc1_current_bound:                     -1
% 3.00/0.98  bmc1_last_solved_bound:                 -1
% 3.00/0.98  bmc1_unsat_core_size:                   -1
% 3.00/0.98  bmc1_unsat_core_parents_size:           -1
% 3.00/0.98  bmc1_merge_next_fun:                    0
% 3.00/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.00/0.98  
% 3.00/0.98  ------ Instantiation
% 3.00/0.98  
% 3.00/0.98  inst_num_of_clauses:                    969
% 3.00/0.98  inst_num_in_passive:                    447
% 3.00/0.98  inst_num_in_active:                     330
% 3.00/0.98  inst_num_in_unprocessed:                193
% 3.00/0.98  inst_num_of_loops:                      470
% 3.00/0.98  inst_num_of_learning_restarts:          0
% 3.00/0.98  inst_num_moves_active_passive:          138
% 3.00/0.98  inst_lit_activity:                      0
% 3.00/0.98  inst_lit_activity_moves:                0
% 3.00/0.98  inst_num_tautologies:                   0
% 3.00/0.98  inst_num_prop_implied:                  0
% 3.00/0.98  inst_num_existing_simplified:           0
% 3.00/0.98  inst_num_eq_res_simplified:             0
% 3.00/0.98  inst_num_child_elim:                    0
% 3.00/0.98  inst_num_of_dismatching_blockings:      642
% 3.00/0.98  inst_num_of_non_proper_insts:           824
% 3.00/0.98  inst_num_of_duplicates:                 0
% 3.00/0.98  inst_inst_num_from_inst_to_res:         0
% 3.00/0.98  inst_dismatching_checking_time:         0.
% 3.00/0.98  
% 3.00/0.98  ------ Resolution
% 3.00/0.98  
% 3.00/0.98  res_num_of_clauses:                     0
% 3.00/0.98  res_num_in_passive:                     0
% 3.00/0.98  res_num_in_active:                      0
% 3.00/0.98  res_num_of_loops:                       168
% 3.00/0.98  res_forward_subset_subsumed:            79
% 3.00/0.98  res_backward_subset_subsumed:           2
% 3.00/0.98  res_forward_subsumed:                   0
% 3.00/0.98  res_backward_subsumed:                  0
% 3.00/0.98  res_forward_subsumption_resolution:     0
% 3.00/0.98  res_backward_subsumption_resolution:    5
% 3.00/0.98  res_clause_to_clause_subsumption:       460
% 3.00/0.98  res_orphan_elimination:                 0
% 3.00/0.98  res_tautology_del:                      74
% 3.00/0.98  res_num_eq_res_simplified:              0
% 3.00/0.98  res_num_sel_changes:                    0
% 3.00/0.98  res_moves_from_active_to_pass:          0
% 3.00/0.98  
% 3.00/0.98  ------ Superposition
% 3.00/0.98  
% 3.00/0.98  sup_time_total:                         0.
% 3.00/0.98  sup_time_generating:                    0.
% 3.00/0.98  sup_time_sim_full:                      0.
% 3.00/0.98  sup_time_sim_immed:                     0.
% 3.00/0.98  
% 3.00/0.98  sup_num_of_clauses:                     140
% 3.00/0.98  sup_num_in_active:                      81
% 3.00/0.98  sup_num_in_passive:                     59
% 3.00/0.98  sup_num_of_loops:                       92
% 3.00/0.98  sup_fw_superposition:                   106
% 3.00/0.98  sup_bw_superposition:                   82
% 3.00/0.98  sup_immediate_simplified:               20
% 3.00/0.98  sup_given_eliminated:                   1
% 3.00/0.98  comparisons_done:                       0
% 3.00/0.98  comparisons_avoided:                    19
% 3.00/0.98  
% 3.00/0.98  ------ Simplifications
% 3.00/0.98  
% 3.00/0.98  
% 3.00/0.98  sim_fw_subset_subsumed:                 17
% 3.00/0.98  sim_bw_subset_subsumed:                 15
% 3.00/0.98  sim_fw_subsumed:                        3
% 3.00/0.98  sim_bw_subsumed:                        7
% 3.00/0.98  sim_fw_subsumption_res:                 0
% 3.00/0.98  sim_bw_subsumption_res:                 0
% 3.00/0.98  sim_tautology_del:                      11
% 3.00/0.98  sim_eq_tautology_del:                   2
% 3.00/0.98  sim_eq_res_simp:                        0
% 3.00/0.98  sim_fw_demodulated:                     0
% 3.00/0.98  sim_bw_demodulated:                     0
% 3.00/0.98  sim_light_normalised:                   0
% 3.00/0.98  sim_joinable_taut:                      0
% 3.00/0.98  sim_joinable_simp:                      0
% 3.00/0.98  sim_ac_normalised:                      0
% 3.00/0.98  sim_smt_subsumption:                    0
% 3.00/0.98  
%------------------------------------------------------------------------------

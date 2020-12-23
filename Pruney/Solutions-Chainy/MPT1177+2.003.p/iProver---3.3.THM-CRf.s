%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:47 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  189 (1410 expanded)
%              Number of clauses        :  117 ( 272 expanded)
%              Number of leaves         :   20 ( 457 expanded)
%              Depth                    :   19
%              Number of atoms          :  939 (13458 expanded)
%              Number of equality atoms :  188 ( 330 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_orders_2(X2,X0,X3)
            | ~ r2_xboole_0(X2,X3) )
          & ( m1_orders_2(X2,X0,X3)
            | r2_xboole_0(X2,X3) )
          & m2_orders_2(X3,X0,X1) )
     => ( ( ~ m1_orders_2(X2,X0,sK4)
          | ~ r2_xboole_0(X2,sK4) )
        & ( m1_orders_2(X2,X0,sK4)
          | r2_xboole_0(X2,sK4) )
        & m2_orders_2(sK4,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,X0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,X0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,X0,X1) )
          & m2_orders_2(X2,X0,X1) )
     => ( ? [X3] :
            ( ( ~ m1_orders_2(sK3,X0,X3)
              | ~ r2_xboole_0(sK3,X3) )
            & ( m1_orders_2(sK3,X0,X3)
              | r2_xboole_0(sK3,X3) )
            & m2_orders_2(X3,X0,X1) )
        & m2_orders_2(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,X0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,X0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,X0,sK2) )
            & m2_orders_2(X2,X0,sK2) )
        & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK1,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK1,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK1,X1) )
              & m2_orders_2(X2,sK1,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ m1_orders_2(sK3,sK1,sK4)
      | ~ r2_xboole_0(sK3,sK4) )
    & ( m1_orders_2(sK3,sK1,sK4)
      | r2_xboole_0(sK3,sK4) )
    & m2_orders_2(sK4,sK1,sK2)
    & m2_orders_2(sK3,sK1,sK2)
    & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f45,f44,f43,f42])).

fof(f71,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
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
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_orders_2(X2,X0,X3)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f49])).

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

fof(f14,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
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
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_21,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1619,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_639,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_640,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_802,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_640,c_23])).

cnf(c_803,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_807,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_27,c_26,c_25,c_24])).

cnf(c_1098,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_807])).

cnf(c_1608,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1098])).

cnf(c_14,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_150,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_11])).

cnf(c_151,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_907,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_151,c_23])).

cnf(c_908,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_912,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_orders_2(X1,sK1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_908,c_27,c_26,c_25,c_24])).

cnf(c_1614,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_1848,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1608,c_1614])).

cnf(c_20,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_58,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_62,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_201,plain,
    ( ~ r2_xboole_0(sK3,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_202,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_371,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_202])).

cnf(c_372,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r1_tarski(sK3,sK4)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_373,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_1759,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_1760,plain,
    ( m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_13,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_931,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_932,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_934,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_932,c_27,c_26,c_25,c_24])).

cnf(c_1775,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_1776,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_1263,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1904,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_1933,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_1270,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1782,plain,
    ( m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X2 != sK4
    | X1 != sK1
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_1932,plain,
    ( m1_orders_2(X0,X1,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X1 != sK1
    | X0 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_2147,plain,
    ( m1_orders_2(sK4,X0,sK4)
    | ~ m1_orders_2(sK3,sK1,sK4)
    | X0 != sK1
    | sK4 != sK4
    | sK4 != sK3 ),
    inference(instantiation,[status(thm)],[c_1932])).

cnf(c_2148,plain,
    ( X0 != sK1
    | sK4 != sK4
    | sK4 != sK3
    | m1_orders_2(sK4,X0,sK4) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2147])).

cnf(c_2150,plain,
    ( sK4 != sK4
    | sK4 != sK3
    | sK1 != sK1
    | m1_orders_2(sK4,sK1,sK4) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_1815,plain,
    ( ~ m1_orders_2(X0,sK1,sK4)
    | ~ m1_orders_2(sK4,sK1,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_2714,plain,
    ( ~ m1_orders_2(sK4,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_2717,plain,
    ( k1_xboole_0 = sK4
    | m1_orders_2(sK4,sK1,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2714])).

cnf(c_1271,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1787,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | X2 != sK2
    | X0 != sK4
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1903,plain,
    ( m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | X0 != sK4
    | X1 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1787])).

cnf(c_2864,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | m2_orders_2(k1_xboole_0,X0,sK2)
    | X0 != sK1
    | sK2 != sK2
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_2865,plain,
    ( X0 != sK1
    | sK2 != sK2
    | k1_xboole_0 != sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(k1_xboole_0,X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2864])).

cnf(c_2867,plain,
    ( sK2 != sK2
    | sK1 != sK1
    | k1_xboole_0 != sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2865])).

cnf(c_1620,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | m1_orders_2(X3,X1,X0)
    | m1_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_567,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | m1_orders_2(X3,X1,X0)
    | m1_orders_2(X0,X1,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_568,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | m1_orders_2(X0,X1,X2)
    | m1_orders_2(X2,X1,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X0 = X2
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_847,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | m1_orders_2(X2,X1,X0)
    | m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X2 = X0
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_568,c_23])).

cnf(c_848,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_852,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | X1 = X0
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_848,c_27,c_26,c_25,c_24])).

cnf(c_1090,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | m1_orders_2(X0,sK1,X1)
    | m1_orders_2(X1,sK1,X0)
    | X1 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_852])).

cnf(c_1610,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1090])).

cnf(c_2581,plain,
    ( sK4 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_1610])).

cnf(c_2835,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_2581])).

cnf(c_34,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_203,plain,
    ( r2_xboole_0(sK3,sK4)
    | m1_orders_2(sK3,sK1,sK4) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_204,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_384,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_204])).

cnf(c_385,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_386,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_2,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_394,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK4 != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_204])).

cnf(c_395,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_396,plain,
    ( sK3 != sK4
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_1762,plain,
    ( ~ m2_orders_2(sK3,sK1,sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_1763,plain,
    ( m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_1917,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(sK4,sK1,sK2)
    | m1_orders_2(X0,sK1,sK4)
    | m1_orders_2(sK4,sK1,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_2107,plain,
    ( ~ m2_orders_2(sK4,sK1,sK2)
    | ~ m2_orders_2(sK3,sK1,sK2)
    | m1_orders_2(sK4,sK1,sK3)
    | m1_orders_2(sK3,sK1,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1917])).

cnf(c_2108,plain,
    ( sK3 = sK4
    | m2_orders_2(sK4,sK1,sK2) != iProver_top
    | m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2107])).

cnf(c_1927,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2118,plain,
    ( ~ r1_tarski(sK4,sK3)
    | ~ r1_tarski(sK3,sK4)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1927])).

cnf(c_2119,plain,
    ( sK3 = sK4
    | r1_tarski(sK4,sK3) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2118])).

cnf(c_2274,plain,
    ( ~ m1_orders_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_2275,plain,
    ( m1_orders_2(sK4,sK1,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2274])).

cnf(c_2905,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2835,c_34,c_35,c_386,c_396,c_1763,c_2108,c_2119,c_2275])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1624,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_357,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_1618,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_3409,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1618])).

cnf(c_15,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_606,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_607,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_823,plain,
    ( ~ m2_orders_2(X0,X1,sK2)
    | ~ m2_orders_2(X2,X1,sK2)
    | ~ r1_xboole_0(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_607,c_23])).

cnf(c_824,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_828,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0)
    | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_27,c_26,c_25,c_24])).

cnf(c_1094,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(X1,sK1,sK2)
    | ~ r1_xboole_0(X1,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_828])).

cnf(c_3483,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m2_orders_2(k1_xboole_0,sK1,sK2)
    | ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1094])).

cnf(c_3489,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3483])).

cnf(c_3542,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1848,c_34,c_35,c_58,c_62,c_373,c_386,c_396,c_1760,c_1763,c_1776,c_1904,c_1933,c_2108,c_2119,c_2150,c_2275,c_2717,c_2867,c_3409,c_3489])).

cnf(c_3549,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1619,c_3542])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.75/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/0.99  
% 1.75/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.75/0.99  
% 1.75/0.99  ------  iProver source info
% 1.75/0.99  
% 1.75/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.75/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.75/0.99  git: non_committed_changes: false
% 1.75/0.99  git: last_make_outside_of_git: false
% 1.75/0.99  
% 1.75/0.99  ------ 
% 1.75/0.99  
% 1.75/0.99  ------ Input Options
% 1.75/0.99  
% 1.75/0.99  --out_options                           all
% 1.75/0.99  --tptp_safe_out                         true
% 1.75/0.99  --problem_path                          ""
% 1.75/0.99  --include_path                          ""
% 1.75/0.99  --clausifier                            res/vclausify_rel
% 1.75/0.99  --clausifier_options                    --mode clausify
% 1.75/0.99  --stdin                                 false
% 1.75/0.99  --stats_out                             all
% 1.75/0.99  
% 1.75/0.99  ------ General Options
% 1.75/0.99  
% 1.75/0.99  --fof                                   false
% 1.75/0.99  --time_out_real                         305.
% 1.75/0.99  --time_out_virtual                      -1.
% 1.75/0.99  --symbol_type_check                     false
% 1.75/0.99  --clausify_out                          false
% 1.75/0.99  --sig_cnt_out                           false
% 1.75/0.99  --trig_cnt_out                          false
% 1.75/0.99  --trig_cnt_out_tolerance                1.
% 1.75/0.99  --trig_cnt_out_sk_spl                   false
% 1.75/0.99  --abstr_cl_out                          false
% 1.75/0.99  
% 1.75/0.99  ------ Global Options
% 1.75/0.99  
% 1.75/0.99  --schedule                              default
% 1.75/0.99  --add_important_lit                     false
% 1.75/0.99  --prop_solver_per_cl                    1000
% 1.75/0.99  --min_unsat_core                        false
% 1.75/0.99  --soft_assumptions                      false
% 1.75/0.99  --soft_lemma_size                       3
% 1.75/0.99  --prop_impl_unit_size                   0
% 1.75/0.99  --prop_impl_unit                        []
% 1.75/0.99  --share_sel_clauses                     true
% 1.75/0.99  --reset_solvers                         false
% 1.75/0.99  --bc_imp_inh                            [conj_cone]
% 1.75/0.99  --conj_cone_tolerance                   3.
% 1.75/0.99  --extra_neg_conj                        none
% 1.75/0.99  --large_theory_mode                     true
% 1.75/0.99  --prolific_symb_bound                   200
% 1.75/0.99  --lt_threshold                          2000
% 1.75/0.99  --clause_weak_htbl                      true
% 1.75/0.99  --gc_record_bc_elim                     false
% 1.75/0.99  
% 1.75/0.99  ------ Preprocessing Options
% 1.75/0.99  
% 1.75/0.99  --preprocessing_flag                    true
% 1.75/0.99  --time_out_prep_mult                    0.1
% 1.75/0.99  --splitting_mode                        input
% 1.75/0.99  --splitting_grd                         true
% 1.75/0.99  --splitting_cvd                         false
% 1.75/0.99  --splitting_cvd_svl                     false
% 1.75/0.99  --splitting_nvd                         32
% 1.75/0.99  --sub_typing                            true
% 1.75/0.99  --prep_gs_sim                           true
% 1.75/0.99  --prep_unflatten                        true
% 1.75/0.99  --prep_res_sim                          true
% 1.75/0.99  --prep_upred                            true
% 1.75/0.99  --prep_sem_filter                       exhaustive
% 1.75/0.99  --prep_sem_filter_out                   false
% 1.75/0.99  --pred_elim                             true
% 1.75/0.99  --res_sim_input                         true
% 1.75/0.99  --eq_ax_congr_red                       true
% 1.75/0.99  --pure_diseq_elim                       true
% 1.75/0.99  --brand_transform                       false
% 1.75/0.99  --non_eq_to_eq                          false
% 1.75/0.99  --prep_def_merge                        true
% 1.75/0.99  --prep_def_merge_prop_impl              false
% 1.75/0.99  --prep_def_merge_mbd                    true
% 1.75/0.99  --prep_def_merge_tr_red                 false
% 1.75/0.99  --prep_def_merge_tr_cl                  false
% 1.75/0.99  --smt_preprocessing                     true
% 1.75/0.99  --smt_ac_axioms                         fast
% 1.75/0.99  --preprocessed_out                      false
% 1.75/0.99  --preprocessed_stats                    false
% 1.75/0.99  
% 1.75/0.99  ------ Abstraction refinement Options
% 1.75/0.99  
% 1.75/0.99  --abstr_ref                             []
% 1.75/0.99  --abstr_ref_prep                        false
% 1.75/0.99  --abstr_ref_until_sat                   false
% 1.75/0.99  --abstr_ref_sig_restrict                funpre
% 1.75/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.75/0.99  --abstr_ref_under                       []
% 1.75/0.99  
% 1.75/0.99  ------ SAT Options
% 1.75/0.99  
% 1.75/0.99  --sat_mode                              false
% 1.75/0.99  --sat_fm_restart_options                ""
% 1.75/0.99  --sat_gr_def                            false
% 1.75/0.99  --sat_epr_types                         true
% 1.75/0.99  --sat_non_cyclic_types                  false
% 1.75/0.99  --sat_finite_models                     false
% 1.75/0.99  --sat_fm_lemmas                         false
% 1.75/0.99  --sat_fm_prep                           false
% 1.75/0.99  --sat_fm_uc_incr                        true
% 1.75/0.99  --sat_out_model                         small
% 1.75/0.99  --sat_out_clauses                       false
% 1.75/0.99  
% 1.75/0.99  ------ QBF Options
% 1.75/0.99  
% 1.75/0.99  --qbf_mode                              false
% 1.75/0.99  --qbf_elim_univ                         false
% 1.75/0.99  --qbf_dom_inst                          none
% 1.75/0.99  --qbf_dom_pre_inst                      false
% 1.75/0.99  --qbf_sk_in                             false
% 1.75/0.99  --qbf_pred_elim                         true
% 1.75/0.99  --qbf_split                             512
% 1.75/0.99  
% 1.75/0.99  ------ BMC1 Options
% 1.75/0.99  
% 1.75/0.99  --bmc1_incremental                      false
% 1.75/0.99  --bmc1_axioms                           reachable_all
% 1.75/0.99  --bmc1_min_bound                        0
% 1.75/0.99  --bmc1_max_bound                        -1
% 1.75/0.99  --bmc1_max_bound_default                -1
% 1.75/0.99  --bmc1_symbol_reachability              true
% 1.75/0.99  --bmc1_property_lemmas                  false
% 1.75/0.99  --bmc1_k_induction                      false
% 1.75/0.99  --bmc1_non_equiv_states                 false
% 1.75/0.99  --bmc1_deadlock                         false
% 1.75/0.99  --bmc1_ucm                              false
% 1.75/0.99  --bmc1_add_unsat_core                   none
% 1.75/0.99  --bmc1_unsat_core_children              false
% 1.75/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.75/0.99  --bmc1_out_stat                         full
% 1.75/0.99  --bmc1_ground_init                      false
% 1.75/0.99  --bmc1_pre_inst_next_state              false
% 1.75/0.99  --bmc1_pre_inst_state                   false
% 1.75/0.99  --bmc1_pre_inst_reach_state             false
% 1.75/0.99  --bmc1_out_unsat_core                   false
% 1.75/0.99  --bmc1_aig_witness_out                  false
% 1.75/0.99  --bmc1_verbose                          false
% 1.75/0.99  --bmc1_dump_clauses_tptp                false
% 1.75/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.75/0.99  --bmc1_dump_file                        -
% 1.75/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.75/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.75/0.99  --bmc1_ucm_extend_mode                  1
% 1.75/0.99  --bmc1_ucm_init_mode                    2
% 1.75/0.99  --bmc1_ucm_cone_mode                    none
% 1.75/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.75/0.99  --bmc1_ucm_relax_model                  4
% 1.75/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.75/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.75/0.99  --bmc1_ucm_layered_model                none
% 1.75/0.99  --bmc1_ucm_max_lemma_size               10
% 1.75/0.99  
% 1.75/0.99  ------ AIG Options
% 1.75/0.99  
% 1.75/0.99  --aig_mode                              false
% 1.75/0.99  
% 1.75/0.99  ------ Instantiation Options
% 1.75/0.99  
% 1.75/0.99  --instantiation_flag                    true
% 1.75/0.99  --inst_sos_flag                         false
% 1.75/0.99  --inst_sos_phase                        true
% 1.75/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.75/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.75/0.99  --inst_lit_sel_side                     num_symb
% 1.75/0.99  --inst_solver_per_active                1400
% 1.75/0.99  --inst_solver_calls_frac                1.
% 1.75/0.99  --inst_passive_queue_type               priority_queues
% 1.75/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.75/0.99  --inst_passive_queues_freq              [25;2]
% 1.75/0.99  --inst_dismatching                      true
% 1.75/0.99  --inst_eager_unprocessed_to_passive     true
% 1.75/0.99  --inst_prop_sim_given                   true
% 1.75/0.99  --inst_prop_sim_new                     false
% 1.75/0.99  --inst_subs_new                         false
% 1.75/0.99  --inst_eq_res_simp                      false
% 1.75/0.99  --inst_subs_given                       false
% 1.75/0.99  --inst_orphan_elimination               true
% 1.75/0.99  --inst_learning_loop_flag               true
% 1.75/0.99  --inst_learning_start                   3000
% 1.75/0.99  --inst_learning_factor                  2
% 1.75/0.99  --inst_start_prop_sim_after_learn       3
% 1.75/0.99  --inst_sel_renew                        solver
% 1.75/0.99  --inst_lit_activity_flag                true
% 1.75/0.99  --inst_restr_to_given                   false
% 1.75/0.99  --inst_activity_threshold               500
% 1.75/0.99  --inst_out_proof                        true
% 1.75/0.99  
% 1.75/0.99  ------ Resolution Options
% 1.75/0.99  
% 1.75/0.99  --resolution_flag                       true
% 1.75/0.99  --res_lit_sel                           adaptive
% 1.75/0.99  --res_lit_sel_side                      none
% 1.75/0.99  --res_ordering                          kbo
% 1.75/0.99  --res_to_prop_solver                    active
% 1.75/0.99  --res_prop_simpl_new                    false
% 1.75/0.99  --res_prop_simpl_given                  true
% 1.75/0.99  --res_passive_queue_type                priority_queues
% 1.75/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.75/0.99  --res_passive_queues_freq               [15;5]
% 1.75/0.99  --res_forward_subs                      full
% 1.75/0.99  --res_backward_subs                     full
% 1.75/0.99  --res_forward_subs_resolution           true
% 1.75/0.99  --res_backward_subs_resolution          true
% 1.75/0.99  --res_orphan_elimination                true
% 1.75/0.99  --res_time_limit                        2.
% 1.75/0.99  --res_out_proof                         true
% 1.75/0.99  
% 1.75/0.99  ------ Superposition Options
% 1.75/0.99  
% 1.75/0.99  --superposition_flag                    true
% 1.75/0.99  --sup_passive_queue_type                priority_queues
% 1.75/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.75/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.75/0.99  --demod_completeness_check              fast
% 1.75/0.99  --demod_use_ground                      true
% 1.75/0.99  --sup_to_prop_solver                    passive
% 1.75/0.99  --sup_prop_simpl_new                    true
% 1.75/0.99  --sup_prop_simpl_given                  true
% 1.75/0.99  --sup_fun_splitting                     false
% 1.75/0.99  --sup_smt_interval                      50000
% 1.75/0.99  
% 1.75/0.99  ------ Superposition Simplification Setup
% 1.75/0.99  
% 1.75/0.99  --sup_indices_passive                   []
% 1.75/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.75/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.99  --sup_full_bw                           [BwDemod]
% 1.75/0.99  --sup_immed_triv                        [TrivRules]
% 1.75/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.75/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.99  --sup_immed_bw_main                     []
% 1.75/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.75/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.99  
% 1.75/0.99  ------ Combination Options
% 1.75/0.99  
% 1.75/0.99  --comb_res_mult                         3
% 1.75/0.99  --comb_sup_mult                         2
% 1.75/0.99  --comb_inst_mult                        10
% 1.75/0.99  
% 1.75/0.99  ------ Debug Options
% 1.75/0.99  
% 1.75/0.99  --dbg_backtrace                         false
% 1.75/0.99  --dbg_dump_prop_clauses                 false
% 1.75/0.99  --dbg_dump_prop_clauses_file            -
% 1.75/0.99  --dbg_out_stat                          false
% 1.75/0.99  ------ Parsing...
% 1.75/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.75/0.99  
% 1.75/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.75/0.99  
% 1.75/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.75/0.99  
% 1.75/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.75/0.99  ------ Proving...
% 1.75/0.99  ------ Problem Properties 
% 1.75/0.99  
% 1.75/0.99  
% 1.75/0.99  clauses                                 18
% 1.75/0.99  conjectures                             2
% 1.75/0.99  EPR                                     12
% 1.75/0.99  Horn                                    14
% 1.75/0.99  unary                                   4
% 1.75/0.99  binary                                  5
% 1.75/0.99  lits                                    46
% 1.75/0.99  lits eq                                 6
% 1.75/0.99  fd_pure                                 0
% 1.75/0.99  fd_pseudo                               0
% 1.75/0.99  fd_cond                                 1
% 1.75/0.99  fd_pseudo_cond                          3
% 1.75/0.99  AC symbols                              0
% 1.75/0.99  
% 1.75/0.99  ------ Schedule dynamic 5 is on 
% 1.75/0.99  
% 1.75/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.75/0.99  
% 1.75/0.99  
% 1.75/0.99  ------ 
% 1.75/0.99  Current options:
% 1.75/0.99  ------ 
% 1.75/0.99  
% 1.75/0.99  ------ Input Options
% 1.75/0.99  
% 1.75/0.99  --out_options                           all
% 1.75/0.99  --tptp_safe_out                         true
% 1.75/0.99  --problem_path                          ""
% 1.75/0.99  --include_path                          ""
% 1.75/0.99  --clausifier                            res/vclausify_rel
% 1.75/0.99  --clausifier_options                    --mode clausify
% 1.75/0.99  --stdin                                 false
% 1.75/0.99  --stats_out                             all
% 1.75/0.99  
% 1.75/0.99  ------ General Options
% 1.75/0.99  
% 1.75/0.99  --fof                                   false
% 1.75/0.99  --time_out_real                         305.
% 1.75/0.99  --time_out_virtual                      -1.
% 1.75/0.99  --symbol_type_check                     false
% 1.75/0.99  --clausify_out                          false
% 1.75/0.99  --sig_cnt_out                           false
% 1.75/0.99  --trig_cnt_out                          false
% 1.75/0.99  --trig_cnt_out_tolerance                1.
% 1.75/0.99  --trig_cnt_out_sk_spl                   false
% 1.75/0.99  --abstr_cl_out                          false
% 1.75/0.99  
% 1.75/0.99  ------ Global Options
% 1.75/0.99  
% 1.75/0.99  --schedule                              default
% 1.75/0.99  --add_important_lit                     false
% 1.75/0.99  --prop_solver_per_cl                    1000
% 1.75/0.99  --min_unsat_core                        false
% 1.75/0.99  --soft_assumptions                      false
% 1.75/0.99  --soft_lemma_size                       3
% 1.75/0.99  --prop_impl_unit_size                   0
% 1.75/0.99  --prop_impl_unit                        []
% 1.75/0.99  --share_sel_clauses                     true
% 1.75/0.99  --reset_solvers                         false
% 1.75/0.99  --bc_imp_inh                            [conj_cone]
% 1.75/0.99  --conj_cone_tolerance                   3.
% 1.75/0.99  --extra_neg_conj                        none
% 1.75/0.99  --large_theory_mode                     true
% 1.75/0.99  --prolific_symb_bound                   200
% 1.75/0.99  --lt_threshold                          2000
% 1.75/0.99  --clause_weak_htbl                      true
% 1.75/0.99  --gc_record_bc_elim                     false
% 1.75/0.99  
% 1.75/0.99  ------ Preprocessing Options
% 1.75/0.99  
% 1.75/0.99  --preprocessing_flag                    true
% 1.75/0.99  --time_out_prep_mult                    0.1
% 1.75/0.99  --splitting_mode                        input
% 1.75/0.99  --splitting_grd                         true
% 1.75/0.99  --splitting_cvd                         false
% 1.75/0.99  --splitting_cvd_svl                     false
% 1.75/0.99  --splitting_nvd                         32
% 1.75/0.99  --sub_typing                            true
% 1.75/0.99  --prep_gs_sim                           true
% 1.75/0.99  --prep_unflatten                        true
% 1.75/0.99  --prep_res_sim                          true
% 1.75/0.99  --prep_upred                            true
% 1.75/0.99  --prep_sem_filter                       exhaustive
% 1.75/0.99  --prep_sem_filter_out                   false
% 1.75/0.99  --pred_elim                             true
% 1.75/0.99  --res_sim_input                         true
% 1.75/0.99  --eq_ax_congr_red                       true
% 1.75/0.99  --pure_diseq_elim                       true
% 1.75/0.99  --brand_transform                       false
% 1.75/0.99  --non_eq_to_eq                          false
% 1.75/0.99  --prep_def_merge                        true
% 1.75/0.99  --prep_def_merge_prop_impl              false
% 1.75/0.99  --prep_def_merge_mbd                    true
% 1.75/0.99  --prep_def_merge_tr_red                 false
% 1.75/0.99  --prep_def_merge_tr_cl                  false
% 1.75/0.99  --smt_preprocessing                     true
% 1.75/0.99  --smt_ac_axioms                         fast
% 1.75/0.99  --preprocessed_out                      false
% 1.75/0.99  --preprocessed_stats                    false
% 1.75/0.99  
% 1.75/0.99  ------ Abstraction refinement Options
% 1.75/0.99  
% 1.75/0.99  --abstr_ref                             []
% 1.75/0.99  --abstr_ref_prep                        false
% 1.75/0.99  --abstr_ref_until_sat                   false
% 1.75/0.99  --abstr_ref_sig_restrict                funpre
% 1.75/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.75/0.99  --abstr_ref_under                       []
% 1.75/0.99  
% 1.75/0.99  ------ SAT Options
% 1.75/0.99  
% 1.75/0.99  --sat_mode                              false
% 1.75/0.99  --sat_fm_restart_options                ""
% 1.75/0.99  --sat_gr_def                            false
% 1.75/0.99  --sat_epr_types                         true
% 1.75/0.99  --sat_non_cyclic_types                  false
% 1.75/0.99  --sat_finite_models                     false
% 1.75/0.99  --sat_fm_lemmas                         false
% 1.75/0.99  --sat_fm_prep                           false
% 1.75/0.99  --sat_fm_uc_incr                        true
% 1.75/0.99  --sat_out_model                         small
% 1.75/0.99  --sat_out_clauses                       false
% 1.75/0.99  
% 1.75/0.99  ------ QBF Options
% 1.75/0.99  
% 1.75/0.99  --qbf_mode                              false
% 1.75/0.99  --qbf_elim_univ                         false
% 1.75/0.99  --qbf_dom_inst                          none
% 1.75/0.99  --qbf_dom_pre_inst                      false
% 1.75/0.99  --qbf_sk_in                             false
% 1.75/0.99  --qbf_pred_elim                         true
% 1.75/0.99  --qbf_split                             512
% 1.75/0.99  
% 1.75/0.99  ------ BMC1 Options
% 1.75/0.99  
% 1.75/0.99  --bmc1_incremental                      false
% 1.75/0.99  --bmc1_axioms                           reachable_all
% 1.75/0.99  --bmc1_min_bound                        0
% 1.75/0.99  --bmc1_max_bound                        -1
% 1.75/0.99  --bmc1_max_bound_default                -1
% 1.75/0.99  --bmc1_symbol_reachability              true
% 1.75/0.99  --bmc1_property_lemmas                  false
% 1.75/0.99  --bmc1_k_induction                      false
% 1.75/0.99  --bmc1_non_equiv_states                 false
% 1.75/0.99  --bmc1_deadlock                         false
% 1.75/0.99  --bmc1_ucm                              false
% 1.75/0.99  --bmc1_add_unsat_core                   none
% 1.75/0.99  --bmc1_unsat_core_children              false
% 1.75/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.75/0.99  --bmc1_out_stat                         full
% 1.75/0.99  --bmc1_ground_init                      false
% 1.75/0.99  --bmc1_pre_inst_next_state              false
% 1.75/0.99  --bmc1_pre_inst_state                   false
% 1.75/0.99  --bmc1_pre_inst_reach_state             false
% 1.75/0.99  --bmc1_out_unsat_core                   false
% 1.75/0.99  --bmc1_aig_witness_out                  false
% 1.75/0.99  --bmc1_verbose                          false
% 1.75/0.99  --bmc1_dump_clauses_tptp                false
% 1.75/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.75/0.99  --bmc1_dump_file                        -
% 1.75/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.75/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.75/0.99  --bmc1_ucm_extend_mode                  1
% 1.75/0.99  --bmc1_ucm_init_mode                    2
% 1.75/0.99  --bmc1_ucm_cone_mode                    none
% 1.75/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.75/0.99  --bmc1_ucm_relax_model                  4
% 1.75/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.75/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.75/0.99  --bmc1_ucm_layered_model                none
% 1.75/0.99  --bmc1_ucm_max_lemma_size               10
% 1.75/0.99  
% 1.75/0.99  ------ AIG Options
% 1.75/0.99  
% 1.75/0.99  --aig_mode                              false
% 1.75/0.99  
% 1.75/0.99  ------ Instantiation Options
% 1.75/0.99  
% 1.75/0.99  --instantiation_flag                    true
% 1.75/0.99  --inst_sos_flag                         false
% 1.75/0.99  --inst_sos_phase                        true
% 1.75/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.75/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.75/0.99  --inst_lit_sel_side                     none
% 1.75/0.99  --inst_solver_per_active                1400
% 1.75/0.99  --inst_solver_calls_frac                1.
% 1.75/0.99  --inst_passive_queue_type               priority_queues
% 1.75/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.75/0.99  --inst_passive_queues_freq              [25;2]
% 1.75/0.99  --inst_dismatching                      true
% 1.75/0.99  --inst_eager_unprocessed_to_passive     true
% 1.75/0.99  --inst_prop_sim_given                   true
% 1.75/0.99  --inst_prop_sim_new                     false
% 1.75/0.99  --inst_subs_new                         false
% 1.75/0.99  --inst_eq_res_simp                      false
% 1.75/0.99  --inst_subs_given                       false
% 1.75/0.99  --inst_orphan_elimination               true
% 1.75/0.99  --inst_learning_loop_flag               true
% 1.75/0.99  --inst_learning_start                   3000
% 1.75/0.99  --inst_learning_factor                  2
% 1.75/0.99  --inst_start_prop_sim_after_learn       3
% 1.75/0.99  --inst_sel_renew                        solver
% 1.75/0.99  --inst_lit_activity_flag                true
% 1.75/0.99  --inst_restr_to_given                   false
% 1.75/0.99  --inst_activity_threshold               500
% 1.75/0.99  --inst_out_proof                        true
% 1.75/0.99  
% 1.75/0.99  ------ Resolution Options
% 1.75/0.99  
% 1.75/0.99  --resolution_flag                       false
% 1.75/0.99  --res_lit_sel                           adaptive
% 1.75/0.99  --res_lit_sel_side                      none
% 1.75/0.99  --res_ordering                          kbo
% 1.75/0.99  --res_to_prop_solver                    active
% 1.75/0.99  --res_prop_simpl_new                    false
% 1.75/0.99  --res_prop_simpl_given                  true
% 1.75/0.99  --res_passive_queue_type                priority_queues
% 1.75/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.75/0.99  --res_passive_queues_freq               [15;5]
% 1.75/0.99  --res_forward_subs                      full
% 1.75/0.99  --res_backward_subs                     full
% 1.75/0.99  --res_forward_subs_resolution           true
% 1.75/0.99  --res_backward_subs_resolution          true
% 1.75/0.99  --res_orphan_elimination                true
% 1.75/0.99  --res_time_limit                        2.
% 1.75/0.99  --res_out_proof                         true
% 1.75/0.99  
% 1.75/0.99  ------ Superposition Options
% 1.75/0.99  
% 1.75/0.99  --superposition_flag                    true
% 1.75/0.99  --sup_passive_queue_type                priority_queues
% 1.75/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.75/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.75/0.99  --demod_completeness_check              fast
% 1.75/0.99  --demod_use_ground                      true
% 1.75/0.99  --sup_to_prop_solver                    passive
% 1.75/0.99  --sup_prop_simpl_new                    true
% 1.75/0.99  --sup_prop_simpl_given                  true
% 1.75/0.99  --sup_fun_splitting                     false
% 1.75/0.99  --sup_smt_interval                      50000
% 1.75/0.99  
% 1.75/0.99  ------ Superposition Simplification Setup
% 1.75/0.99  
% 1.75/0.99  --sup_indices_passive                   []
% 1.75/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.75/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.99  --sup_full_bw                           [BwDemod]
% 1.75/0.99  --sup_immed_triv                        [TrivRules]
% 1.75/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.75/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.99  --sup_immed_bw_main                     []
% 1.75/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.75/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.99  
% 1.75/0.99  ------ Combination Options
% 1.75/0.99  
% 1.75/0.99  --comb_res_mult                         3
% 1.75/0.99  --comb_sup_mult                         2
% 1.75/0.99  --comb_inst_mult                        10
% 1.75/0.99  
% 1.75/0.99  ------ Debug Options
% 1.75/0.99  
% 1.75/0.99  --dbg_backtrace                         false
% 1.75/0.99  --dbg_dump_prop_clauses                 false
% 1.75/0.99  --dbg_dump_prop_clauses_file            -
% 1.75/0.99  --dbg_out_stat                          false
% 1.75/0.99  
% 1.75/0.99  
% 1.75/0.99  
% 1.75/0.99  
% 1.75/0.99  ------ Proving...
% 1.75/0.99  
% 1.75/0.99  
% 1.75/0.99  % SZS status Theorem for theBenchmark.p
% 1.75/0.99  
% 1.75/0.99   Resolution empty clause
% 1.75/0.99  
% 1.75/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.75/0.99  
% 1.75/0.99  fof(f12,conjecture,(
% 1.75/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f13,negated_conjecture,(
% 1.75/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.75/0.99    inference(negated_conjecture,[],[f12])).
% 1.75/0.99  
% 1.75/0.99  fof(f31,plain,(
% 1.75/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.75/0.99    inference(ennf_transformation,[],[f13])).
% 1.75/0.99  
% 1.75/0.99  fof(f32,plain,(
% 1.75/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.75/0.99    inference(flattening,[],[f31])).
% 1.75/0.99  
% 1.75/0.99  fof(f40,plain,(
% 1.75/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.75/0.99    inference(nnf_transformation,[],[f32])).
% 1.75/0.99  
% 1.75/0.99  fof(f41,plain,(
% 1.75/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.75/0.99    inference(flattening,[],[f40])).
% 1.75/0.99  
% 1.75/0.99  fof(f45,plain,(
% 1.75/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 1.75/0.99    introduced(choice_axiom,[])).
% 1.75/0.99  
% 1.75/0.99  fof(f44,plain,(
% 1.75/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 1.75/0.99    introduced(choice_axiom,[])).
% 1.75/0.99  
% 1.75/0.99  fof(f43,plain,(
% 1.75/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 1.75/0.99    introduced(choice_axiom,[])).
% 1.75/0.99  
% 1.75/0.99  fof(f42,plain,(
% 1.75/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.75/0.99    introduced(choice_axiom,[])).
% 1.75/0.99  
% 1.75/0.99  fof(f46,plain,(
% 1.75/0.99    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f41,f45,f44,f43,f42])).
% 1.75/0.99  
% 1.75/0.99  fof(f71,plain,(
% 1.75/0.99    m2_orders_2(sK3,sK1,sK2)),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f7,axiom,(
% 1.75/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f16,plain,(
% 1.75/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.75/0.99    inference(pure_predicate_removal,[],[f7])).
% 1.75/0.99  
% 1.75/0.99  fof(f21,plain,(
% 1.75/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.75/0.99    inference(ennf_transformation,[],[f16])).
% 1.75/0.99  
% 1.75/0.99  fof(f22,plain,(
% 1.75/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/0.99    inference(flattening,[],[f21])).
% 1.75/0.99  
% 1.75/0.99  fof(f59,plain,(
% 1.75/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f22])).
% 1.75/0.99  
% 1.75/0.99  fof(f70,plain,(
% 1.75/0.99    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f69,plain,(
% 1.75/0.99    l1_orders_2(sK1)),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f65,plain,(
% 1.75/0.99    ~v2_struct_0(sK1)),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f66,plain,(
% 1.75/0.99    v3_orders_2(sK1)),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f67,plain,(
% 1.75/0.99    v4_orders_2(sK1)),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f68,plain,(
% 1.75/0.99    v5_orders_2(sK1)),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f9,axiom,(
% 1.75/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f25,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.75/0.99    inference(ennf_transformation,[],[f9])).
% 1.75/0.99  
% 1.75/0.99  fof(f26,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/0.99    inference(flattening,[],[f25])).
% 1.75/0.99  
% 1.75/0.99  fof(f61,plain,(
% 1.75/0.99    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f26])).
% 1.75/0.99  
% 1.75/0.99  fof(f6,axiom,(
% 1.75/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f19,plain,(
% 1.75/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.75/0.99    inference(ennf_transformation,[],[f6])).
% 1.75/0.99  
% 1.75/0.99  fof(f20,plain,(
% 1.75/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/0.99    inference(flattening,[],[f19])).
% 1.75/0.99  
% 1.75/0.99  fof(f58,plain,(
% 1.75/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f20])).
% 1.75/0.99  
% 1.75/0.99  fof(f72,plain,(
% 1.75/0.99    m2_orders_2(sK4,sK1,sK2)),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f5,axiom,(
% 1.75/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f37,plain,(
% 1.75/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.99    inference(nnf_transformation,[],[f5])).
% 1.75/0.99  
% 1.75/0.99  fof(f38,plain,(
% 1.75/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.99    inference(flattening,[],[f37])).
% 1.75/0.99  
% 1.75/0.99  fof(f55,plain,(
% 1.75/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.75/0.99    inference(cnf_transformation,[],[f38])).
% 1.75/0.99  
% 1.75/0.99  fof(f77,plain,(
% 1.75/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.75/0.99    inference(equality_resolution,[],[f55])).
% 1.75/0.99  
% 1.75/0.99  fof(f57,plain,(
% 1.75/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f38])).
% 1.75/0.99  
% 1.75/0.99  fof(f2,axiom,(
% 1.75/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f33,plain,(
% 1.75/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.75/0.99    inference(nnf_transformation,[],[f2])).
% 1.75/0.99  
% 1.75/0.99  fof(f34,plain,(
% 1.75/0.99    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.75/0.99    inference(flattening,[],[f33])).
% 1.75/0.99  
% 1.75/0.99  fof(f50,plain,(
% 1.75/0.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f34])).
% 1.75/0.99  
% 1.75/0.99  fof(f74,plain,(
% 1.75/0.99    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f8,axiom,(
% 1.75/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f23,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.75/0.99    inference(ennf_transformation,[],[f8])).
% 1.75/0.99  
% 1.75/0.99  fof(f24,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/0.99    inference(flattening,[],[f23])).
% 1.75/0.99  
% 1.75/0.99  fof(f60,plain,(
% 1.75/0.99    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f24])).
% 1.75/0.99  
% 1.75/0.99  fof(f11,axiom,(
% 1.75/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f29,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.75/0.99    inference(ennf_transformation,[],[f11])).
% 1.75/0.99  
% 1.75/0.99  fof(f30,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/0.99    inference(flattening,[],[f29])).
% 1.75/0.99  
% 1.75/0.99  fof(f39,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/0.99    inference(nnf_transformation,[],[f30])).
% 1.75/0.99  
% 1.75/0.99  fof(f64,plain,(
% 1.75/0.99    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f39])).
% 1.75/0.99  
% 1.75/0.99  fof(f48,plain,(
% 1.75/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f34])).
% 1.75/0.99  
% 1.75/0.99  fof(f73,plain,(
% 1.75/0.99    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 1.75/0.99    inference(cnf_transformation,[],[f46])).
% 1.75/0.99  
% 1.75/0.99  fof(f49,plain,(
% 1.75/0.99    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f34])).
% 1.75/0.99  
% 1.75/0.99  fof(f75,plain,(
% 1.75/0.99    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 1.75/0.99    inference(equality_resolution,[],[f49])).
% 1.75/0.99  
% 1.75/0.99  fof(f4,axiom,(
% 1.75/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f14,plain,(
% 1.75/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.75/0.99    inference(rectify,[],[f4])).
% 1.75/0.99  
% 1.75/0.99  fof(f18,plain,(
% 1.75/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.75/0.99    inference(ennf_transformation,[],[f14])).
% 1.75/0.99  
% 1.75/0.99  fof(f35,plain,(
% 1.75/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.75/0.99    introduced(choice_axiom,[])).
% 1.75/0.99  
% 1.75/0.99  fof(f36,plain,(
% 1.75/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f35])).
% 1.75/0.99  
% 1.75/0.99  fof(f53,plain,(
% 1.75/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f36])).
% 1.75/0.99  
% 1.75/0.99  fof(f1,axiom,(
% 1.75/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f15,plain,(
% 1.75/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.75/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 1.75/0.99  
% 1.75/0.99  fof(f17,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.75/0.99    inference(ennf_transformation,[],[f15])).
% 1.75/0.99  
% 1.75/0.99  fof(f47,plain,(
% 1.75/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f17])).
% 1.75/0.99  
% 1.75/0.99  fof(f3,axiom,(
% 1.75/0.99    v1_xboole_0(k1_xboole_0)),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f51,plain,(
% 1.75/0.99    v1_xboole_0(k1_xboole_0)),
% 1.75/0.99    inference(cnf_transformation,[],[f3])).
% 1.75/0.99  
% 1.75/0.99  fof(f10,axiom,(
% 1.75/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 1.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.99  
% 1.75/0.99  fof(f27,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.75/0.99    inference(ennf_transformation,[],[f10])).
% 1.75/0.99  
% 1.75/0.99  fof(f28,plain,(
% 1.75/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.75/0.99    inference(flattening,[],[f27])).
% 1.75/0.99  
% 1.75/0.99  fof(f62,plain,(
% 1.75/0.99    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.75/0.99    inference(cnf_transformation,[],[f28])).
% 1.75/0.99  
% 1.75/0.99  cnf(c_21,negated_conjecture,
% 1.75/0.99      ( m2_orders_2(sK3,sK1,sK2) ),
% 1.75/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_1619,plain,
% 1.75/0.99      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 1.75/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_12,plain,
% 1.75/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.75/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | ~ l1_orders_2(X1) ),
% 1.75/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_22,negated_conjecture,
% 1.75/0.99      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 1.75/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_639,plain,
% 1.75/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | ~ l1_orders_2(X1)
% 1.75/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.75/0.99      | sK2 != X2 ),
% 1.75/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_640,plain,
% 1.75/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | ~ l1_orders_2(X1)
% 1.75/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.75/0.99      inference(unflattening,[status(thm)],[c_639]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_23,negated_conjecture,
% 1.75/0.99      ( l1_orders_2(sK1) ),
% 1.75/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_802,plain,
% 1.75/0.99      ( ~ m2_orders_2(X0,X1,sK2)
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.75/0.99      | sK1 != X1 ),
% 1.75/0.99      inference(resolution_lifted,[status(thm)],[c_640,c_23]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_803,plain,
% 1.75/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/0.99      | v2_struct_0(sK1)
% 1.75/0.99      | ~ v3_orders_2(sK1)
% 1.75/0.99      | ~ v4_orders_2(sK1)
% 1.75/0.99      | ~ v5_orders_2(sK1)
% 1.75/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.75/0.99      inference(unflattening,[status(thm)],[c_802]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_27,negated_conjecture,
% 1.75/0.99      ( ~ v2_struct_0(sK1) ),
% 1.75/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_26,negated_conjecture,
% 1.75/0.99      ( v3_orders_2(sK1) ),
% 1.75/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_25,negated_conjecture,
% 1.75/0.99      ( v4_orders_2(sK1) ),
% 1.75/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_24,negated_conjecture,
% 1.75/0.99      ( v5_orders_2(sK1) ),
% 1.75/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_807,plain,
% 1.75/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/0.99      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.75/0.99      inference(global_propositional_subsumption,
% 1.75/0.99                [status(thm)],
% 1.75/0.99                [c_803,c_27,c_26,c_25,c_24]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_1098,plain,
% 1.75/0.99      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.75/0.99      inference(equality_resolution_simp,[status(thm)],[c_807]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_1608,plain,
% 1.75/0.99      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.75/0.99      inference(predicate_to_equality,[status(thm)],[c_1098]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_14,plain,
% 1.75/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.75/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.75/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | ~ l1_orders_2(X1)
% 1.75/0.99      | k1_xboole_0 = X2 ),
% 1.75/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_11,plain,
% 1.75/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.75/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | ~ l1_orders_2(X1) ),
% 1.75/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_150,plain,
% 1.75/0.99      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.75/0.99      | ~ m1_orders_2(X0,X1,X2)
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | ~ l1_orders_2(X1)
% 1.75/0.99      | k1_xboole_0 = X2 ),
% 1.75/0.99      inference(global_propositional_subsumption,[status(thm)],[c_14,c_11]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_151,plain,
% 1.75/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.75/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.75/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | ~ l1_orders_2(X1)
% 1.75/0.99      | k1_xboole_0 = X0 ),
% 1.75/0.99      inference(renaming,[status(thm)],[c_150]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_907,plain,
% 1.75/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.75/0.99      | ~ m1_orders_2(X2,X1,X0)
% 1.75/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | sK1 != X1
% 1.75/0.99      | k1_xboole_0 = X2 ),
% 1.75/0.99      inference(resolution_lifted,[status(thm)],[c_151,c_23]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_908,plain,
% 1.75/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.75/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 1.75/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/0.99      | v2_struct_0(sK1)
% 1.75/0.99      | ~ v3_orders_2(sK1)
% 1.75/0.99      | ~ v4_orders_2(sK1)
% 1.75/0.99      | ~ v5_orders_2(sK1)
% 1.75/0.99      | k1_xboole_0 = X1 ),
% 1.75/0.99      inference(unflattening,[status(thm)],[c_907]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_912,plain,
% 1.75/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.75/0.99      | ~ m1_orders_2(X1,sK1,X0)
% 1.75/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/0.99      | k1_xboole_0 = X1 ),
% 1.75/0.99      inference(global_propositional_subsumption,
% 1.75/0.99                [status(thm)],
% 1.75/0.99                [c_908,c_27,c_26,c_25,c_24]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_1614,plain,
% 1.75/0.99      ( k1_xboole_0 = X0
% 1.75/0.99      | m1_orders_2(X0,sK1,X1) != iProver_top
% 1.75/0.99      | m1_orders_2(X1,sK1,X0) != iProver_top
% 1.75/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.75/0.99      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_1848,plain,
% 1.75/0.99      ( k1_xboole_0 = X0
% 1.75/0.99      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.75/0.99      | m1_orders_2(X1,sK1,X0) != iProver_top
% 1.75/0.99      | m1_orders_2(X0,sK1,X1) != iProver_top ),
% 1.75/0.99      inference(superposition,[status(thm)],[c_1608,c_1614]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_20,negated_conjecture,
% 1.75/0.99      ( m2_orders_2(sK4,sK1,sK2) ),
% 1.75/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_35,plain,
% 1.75/0.99      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.75/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_10,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f77]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_58,plain,
% 1.75/0.99      ( r1_tarski(sK1,sK1) ),
% 1.75/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_8,plain,
% 1.75/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.75/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_62,plain,
% 1.75/0.99      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 1.75/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_1,plain,
% 1.75/0.99      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X0 = X1 ),
% 1.75/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_18,negated_conjecture,
% 1.75/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.75/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_201,plain,
% 1.75/0.99      ( ~ r2_xboole_0(sK3,sK4) | ~ m1_orders_2(sK3,sK1,sK4) ),
% 1.75/0.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_202,plain,
% 1.75/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 1.75/0.99      inference(renaming,[status(thm)],[c_201]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_371,plain,
% 1.75/0.99      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.75/0.99      | ~ r1_tarski(X0,X1)
% 1.75/0.99      | X1 = X0
% 1.75/0.99      | sK4 != X1
% 1.75/0.99      | sK3 != X0 ),
% 1.75/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_202]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_372,plain,
% 1.75/0.99      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r1_tarski(sK3,sK4) | sK4 = sK3 ),
% 1.75/0.99      inference(unflattening,[status(thm)],[c_371]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_373,plain,
% 1.75/0.99      ( sK4 = sK3
% 1.75/0.99      | m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.75/0.99      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.75/0.99      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_1759,plain,
% 1.75/0.99      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.75/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.75/0.99      inference(instantiation,[status(thm)],[c_1098]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_1760,plain,
% 1.75/0.99      ( m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.75/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.75/0.99      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_13,plain,
% 1.75/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.75/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | r1_tarski(X0,X2)
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | ~ l1_orders_2(X1) ),
% 1.75/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_931,plain,
% 1.75/0.99      ( ~ m1_orders_2(X0,X1,X2)
% 1.75/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.75/0.99      | r1_tarski(X0,X2)
% 1.75/0.99      | v2_struct_0(X1)
% 1.75/0.99      | ~ v3_orders_2(X1)
% 1.75/0.99      | ~ v4_orders_2(X1)
% 1.75/0.99      | ~ v5_orders_2(X1)
% 1.75/0.99      | sK1 != X1 ),
% 1.75/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 1.75/0.99  
% 1.75/0.99  cnf(c_932,plain,
% 1.75/0.99      ( ~ m1_orders_2(X0,sK1,X1)
% 1.75/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/0.99      | r1_tarski(X0,X1)
% 1.75/0.99      | v2_struct_0(sK1)
% 1.75/0.99      | ~ v3_orders_2(sK1)
% 1.75/0.99      | ~ v4_orders_2(sK1)
% 1.75/0.99      | ~ v5_orders_2(sK1) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_931]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_934,plain,
% 1.75/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.75/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/1.00      | r1_tarski(X0,X1) ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_932,c_27,c_26,c_25,c_24]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1775,plain,
% 1.75/1.00      ( ~ m1_orders_2(sK3,sK1,sK4)
% 1.75/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/1.00      | r1_tarski(sK3,sK4) ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_934]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1776,plain,
% 1.75/1.00      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 1.75/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.75/1.00      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1263,plain,( X0 = X0 ),theory(equality) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1904,plain,
% 1.75/1.00      ( sK2 = sK2 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1263]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1933,plain,
% 1.75/1.00      ( sK4 = sK4 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1263]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1270,plain,
% 1.75/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.75/1.00      | m1_orders_2(X3,X4,X5)
% 1.75/1.00      | X3 != X0
% 1.75/1.00      | X4 != X1
% 1.75/1.00      | X5 != X2 ),
% 1.75/1.00      theory(equality) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1782,plain,
% 1.75/1.00      ( m1_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ m1_orders_2(sK3,sK1,sK4)
% 1.75/1.00      | X2 != sK4
% 1.75/1.00      | X1 != sK1
% 1.75/1.00      | X0 != sK3 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1270]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1932,plain,
% 1.75/1.00      ( m1_orders_2(X0,X1,sK4)
% 1.75/1.00      | ~ m1_orders_2(sK3,sK1,sK4)
% 1.75/1.00      | X1 != sK1
% 1.75/1.00      | X0 != sK3
% 1.75/1.00      | sK4 != sK4 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1782]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2147,plain,
% 1.75/1.00      ( m1_orders_2(sK4,X0,sK4)
% 1.75/1.00      | ~ m1_orders_2(sK3,sK1,sK4)
% 1.75/1.00      | X0 != sK1
% 1.75/1.00      | sK4 != sK4
% 1.75/1.00      | sK4 != sK3 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1932]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2148,plain,
% 1.75/1.00      ( X0 != sK1
% 1.75/1.00      | sK4 != sK4
% 1.75/1.00      | sK4 != sK3
% 1.75/1.00      | m1_orders_2(sK4,X0,sK4) = iProver_top
% 1.75/1.00      | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2147]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2150,plain,
% 1.75/1.00      ( sK4 != sK4
% 1.75/1.00      | sK4 != sK3
% 1.75/1.00      | sK1 != sK1
% 1.75/1.00      | m1_orders_2(sK4,sK1,sK4) = iProver_top
% 1.75/1.00      | m1_orders_2(sK3,sK1,sK4) != iProver_top ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_2148]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1815,plain,
% 1.75/1.00      ( ~ m1_orders_2(X0,sK1,sK4)
% 1.75/1.00      | ~ m1_orders_2(sK4,sK1,X0)
% 1.75/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/1.00      | k1_xboole_0 = sK4 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_912]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2714,plain,
% 1.75/1.00      ( ~ m1_orders_2(sK4,sK1,sK4)
% 1.75/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/1.00      | k1_xboole_0 = sK4 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1815]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2717,plain,
% 1.75/1.00      ( k1_xboole_0 = sK4
% 1.75/1.00      | m1_orders_2(sK4,sK1,sK4) != iProver_top
% 1.75/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2714]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1271,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.75/1.00      | m2_orders_2(X3,X4,X5)
% 1.75/1.00      | X3 != X0
% 1.75/1.00      | X4 != X1
% 1.75/1.00      | X5 != X2 ),
% 1.75/1.00      theory(equality) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1787,plain,
% 1.75/1.00      ( m2_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.75/1.00      | X2 != sK2
% 1.75/1.00      | X0 != sK4
% 1.75/1.00      | X1 != sK1 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1271]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1903,plain,
% 1.75/1.00      ( m2_orders_2(X0,X1,sK2)
% 1.75/1.00      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.75/1.00      | X0 != sK4
% 1.75/1.00      | X1 != sK1
% 1.75/1.00      | sK2 != sK2 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1787]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2864,plain,
% 1.75/1.00      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.75/1.00      | m2_orders_2(k1_xboole_0,X0,sK2)
% 1.75/1.00      | X0 != sK1
% 1.75/1.00      | sK2 != sK2
% 1.75/1.00      | k1_xboole_0 != sK4 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1903]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2865,plain,
% 1.75/1.00      ( X0 != sK1
% 1.75/1.00      | sK2 != sK2
% 1.75/1.00      | k1_xboole_0 != sK4
% 1.75/1.00      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.75/1.00      | m2_orders_2(k1_xboole_0,X0,sK2) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2864]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2867,plain,
% 1.75/1.00      ( sK2 != sK2
% 1.75/1.00      | sK1 != sK1
% 1.75/1.00      | k1_xboole_0 != sK4
% 1.75/1.00      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.75/1.00      | m2_orders_2(k1_xboole_0,sK1,sK2) = iProver_top ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_2865]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1620,plain,
% 1.75/1.00      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_16,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.75/1.00      | m1_orders_2(X3,X1,X0)
% 1.75/1.00      | m1_orders_2(X0,X1,X3)
% 1.75/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.75/1.00      | v2_struct_0(X1)
% 1.75/1.00      | ~ v3_orders_2(X1)
% 1.75/1.00      | ~ v4_orders_2(X1)
% 1.75/1.00      | ~ v5_orders_2(X1)
% 1.75/1.00      | ~ l1_orders_2(X1)
% 1.75/1.00      | X3 = X0 ),
% 1.75/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_567,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.75/1.00      | m1_orders_2(X3,X1,X0)
% 1.75/1.00      | m1_orders_2(X0,X1,X3)
% 1.75/1.00      | v2_struct_0(X1)
% 1.75/1.00      | ~ v3_orders_2(X1)
% 1.75/1.00      | ~ v4_orders_2(X1)
% 1.75/1.00      | ~ v5_orders_2(X1)
% 1.75/1.00      | ~ l1_orders_2(X1)
% 1.75/1.00      | X3 = X0
% 1.75/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.75/1.00      | sK2 != X2 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_568,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 1.75/1.00      | m1_orders_2(X0,X1,X2)
% 1.75/1.00      | m1_orders_2(X2,X1,X0)
% 1.75/1.00      | v2_struct_0(X1)
% 1.75/1.00      | ~ v3_orders_2(X1)
% 1.75/1.00      | ~ v4_orders_2(X1)
% 1.75/1.00      | ~ v5_orders_2(X1)
% 1.75/1.00      | ~ l1_orders_2(X1)
% 1.75/1.00      | X0 = X2
% 1.75/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_567]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_847,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 1.75/1.00      | m1_orders_2(X2,X1,X0)
% 1.75/1.00      | m1_orders_2(X0,X1,X2)
% 1.75/1.00      | v2_struct_0(X1)
% 1.75/1.00      | ~ v3_orders_2(X1)
% 1.75/1.00      | ~ v4_orders_2(X1)
% 1.75/1.00      | ~ v5_orders_2(X1)
% 1.75/1.00      | X2 = X0
% 1.75/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.75/1.00      | sK1 != X1 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_568,c_23]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_848,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 1.75/1.00      | m1_orders_2(X0,sK1,X1)
% 1.75/1.00      | m1_orders_2(X1,sK1,X0)
% 1.75/1.00      | v2_struct_0(sK1)
% 1.75/1.00      | ~ v3_orders_2(sK1)
% 1.75/1.00      | ~ v4_orders_2(sK1)
% 1.75/1.00      | ~ v5_orders_2(sK1)
% 1.75/1.00      | X1 = X0
% 1.75/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_847]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_852,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 1.75/1.00      | m1_orders_2(X0,sK1,X1)
% 1.75/1.00      | m1_orders_2(X1,sK1,X0)
% 1.75/1.00      | X1 = X0
% 1.75/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_848,c_27,c_26,c_25,c_24]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1090,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 1.75/1.00      | m1_orders_2(X0,sK1,X1)
% 1.75/1.00      | m1_orders_2(X1,sK1,X0)
% 1.75/1.00      | X1 = X0 ),
% 1.75/1.00      inference(equality_resolution_simp,[status(thm)],[c_852]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1610,plain,
% 1.75/1.00      ( X0 = X1
% 1.75/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 1.75/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.75/1.00      | m1_orders_2(X1,sK1,X0) = iProver_top
% 1.75/1.00      | m1_orders_2(X0,sK1,X1) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1090]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2581,plain,
% 1.75/1.00      ( sK4 = X0
% 1.75/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.75/1.00      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 1.75/1.00      | m1_orders_2(sK4,sK1,X0) = iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_1620,c_1610]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2835,plain,
% 1.75/1.00      ( sK4 = sK3
% 1.75/1.00      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.75/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_1619,c_2581]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_34,plain,
% 1.75/1.00      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3,plain,
% 1.75/1.00      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 1.75/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_19,negated_conjecture,
% 1.75/1.00      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.75/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_203,plain,
% 1.75/1.00      ( r2_xboole_0(sK3,sK4) | m1_orders_2(sK3,sK1,sK4) ),
% 1.75/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_204,plain,
% 1.75/1.00      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 1.75/1.00      inference(renaming,[status(thm)],[c_203]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_384,plain,
% 1.75/1.00      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(X0,X1) | sK4 != X1 | sK3 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_204]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_385,plain,
% 1.75/1.00      ( m1_orders_2(sK3,sK1,sK4) | r1_tarski(sK3,sK4) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_384]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_386,plain,
% 1.75/1.00      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 1.75/1.00      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2,plain,
% 1.75/1.00      ( ~ r2_xboole_0(X0,X0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_394,plain,
% 1.75/1.00      ( m1_orders_2(sK3,sK1,sK4) | sK4 != X0 | sK3 != X0 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_204]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_395,plain,
% 1.75/1.00      ( m1_orders_2(sK3,sK1,sK4) | sK3 != sK4 ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_394]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_396,plain,
% 1.75/1.00      ( sK3 != sK4 | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1762,plain,
% 1.75/1.00      ( ~ m2_orders_2(sK3,sK1,sK2)
% 1.75/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1098]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1763,plain,
% 1.75/1.00      ( m2_orders_2(sK3,sK1,sK2) != iProver_top
% 1.75/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1762]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1917,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/1.00      | ~ m2_orders_2(sK4,sK1,sK2)
% 1.75/1.00      | m1_orders_2(X0,sK1,sK4)
% 1.75/1.00      | m1_orders_2(sK4,sK1,X0)
% 1.75/1.00      | X0 = sK4 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1090]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2107,plain,
% 1.75/1.00      ( ~ m2_orders_2(sK4,sK1,sK2)
% 1.75/1.00      | ~ m2_orders_2(sK3,sK1,sK2)
% 1.75/1.00      | m1_orders_2(sK4,sK1,sK3)
% 1.75/1.00      | m1_orders_2(sK3,sK1,sK4)
% 1.75/1.00      | sK3 = sK4 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1917]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2108,plain,
% 1.75/1.00      ( sK3 = sK4
% 1.75/1.00      | m2_orders_2(sK4,sK1,sK2) != iProver_top
% 1.75/1.00      | m2_orders_2(sK3,sK1,sK2) != iProver_top
% 1.75/1.00      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 1.75/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2107]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1927,plain,
% 1.75/1.00      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2118,plain,
% 1.75/1.00      ( ~ r1_tarski(sK4,sK3) | ~ r1_tarski(sK3,sK4) | sK3 = sK4 ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1927]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2119,plain,
% 1.75/1.00      ( sK3 = sK4
% 1.75/1.00      | r1_tarski(sK4,sK3) != iProver_top
% 1.75/1.00      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2118]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2274,plain,
% 1.75/1.00      ( ~ m1_orders_2(sK4,sK1,sK3)
% 1.75/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.75/1.00      | r1_tarski(sK4,sK3) ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_934]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2275,plain,
% 1.75/1.00      ( m1_orders_2(sK4,sK1,sK3) != iProver_top
% 1.75/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.75/1.00      | r1_tarski(sK4,sK3) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2274]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_2905,plain,
% 1.75/1.00      ( m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_2835,c_34,c_35,c_386,c_396,c_1763,c_2108,c_2119,c_2275]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_6,plain,
% 1.75/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK0(X0,X1),X1) ),
% 1.75/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1624,plain,
% 1.75/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 1.75/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_0,plain,
% 1.75/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.75/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_4,plain,
% 1.75/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.75/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_356,plain,
% 1.75/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_357,plain,
% 1.75/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_356]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1618,plain,
% 1.75/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3409,plain,
% 1.75/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_1624,c_1618]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_15,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.75/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.75/1.00      | ~ r1_xboole_0(X0,X3)
% 1.75/1.00      | v2_struct_0(X1)
% 1.75/1.00      | ~ v3_orders_2(X1)
% 1.75/1.00      | ~ v4_orders_2(X1)
% 1.75/1.00      | ~ v5_orders_2(X1)
% 1.75/1.00      | ~ l1_orders_2(X1) ),
% 1.75/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_606,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 1.75/1.00      | ~ m2_orders_2(X3,X1,X2)
% 1.75/1.00      | ~ r1_xboole_0(X0,X3)
% 1.75/1.00      | v2_struct_0(X1)
% 1.75/1.00      | ~ v3_orders_2(X1)
% 1.75/1.00      | ~ v4_orders_2(X1)
% 1.75/1.00      | ~ v5_orders_2(X1)
% 1.75/1.00      | ~ l1_orders_2(X1)
% 1.75/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.75/1.00      | sK2 != X2 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_607,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 1.75/1.00      | ~ r1_xboole_0(X2,X0)
% 1.75/1.00      | v2_struct_0(X1)
% 1.75/1.00      | ~ v3_orders_2(X1)
% 1.75/1.00      | ~ v4_orders_2(X1)
% 1.75/1.00      | ~ v5_orders_2(X1)
% 1.75/1.00      | ~ l1_orders_2(X1)
% 1.75/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_606]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_823,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,X1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X2,X1,sK2)
% 1.75/1.00      | ~ r1_xboole_0(X2,X0)
% 1.75/1.00      | v2_struct_0(X1)
% 1.75/1.00      | ~ v3_orders_2(X1)
% 1.75/1.00      | ~ v4_orders_2(X1)
% 1.75/1.00      | ~ v5_orders_2(X1)
% 1.75/1.00      | k1_orders_1(u1_struct_0(X1)) != k1_orders_1(u1_struct_0(sK1))
% 1.75/1.00      | sK1 != X1 ),
% 1.75/1.00      inference(resolution_lifted,[status(thm)],[c_607,c_23]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_824,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 1.75/1.00      | ~ r1_xboole_0(X1,X0)
% 1.75/1.00      | v2_struct_0(sK1)
% 1.75/1.00      | ~ v3_orders_2(sK1)
% 1.75/1.00      | ~ v4_orders_2(sK1)
% 1.75/1.00      | ~ v5_orders_2(sK1)
% 1.75/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.75/1.00      inference(unflattening,[status(thm)],[c_823]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_828,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 1.75/1.00      | ~ r1_xboole_0(X1,X0)
% 1.75/1.00      | k1_orders_1(u1_struct_0(sK1)) != k1_orders_1(u1_struct_0(sK1)) ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_824,c_27,c_26,c_25,c_24]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_1094,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/1.00      | ~ m2_orders_2(X1,sK1,sK2)
% 1.75/1.00      | ~ r1_xboole_0(X1,X0) ),
% 1.75/1.00      inference(equality_resolution_simp,[status(thm)],[c_828]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3483,plain,
% 1.75/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 1.75/1.00      | ~ m2_orders_2(k1_xboole_0,sK1,sK2)
% 1.75/1.00      | ~ r1_xboole_0(X0,k1_xboole_0) ),
% 1.75/1.00      inference(instantiation,[status(thm)],[c_1094]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3489,plain,
% 1.75/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 1.75/1.00      | m2_orders_2(k1_xboole_0,sK1,sK2) != iProver_top
% 1.75/1.00      | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 1.75/1.00      inference(predicate_to_equality,[status(thm)],[c_3483]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3542,plain,
% 1.75/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 1.75/1.00      inference(global_propositional_subsumption,
% 1.75/1.00                [status(thm)],
% 1.75/1.00                [c_1848,c_34,c_35,c_58,c_62,c_373,c_386,c_396,c_1760,c_1763,
% 1.75/1.00                 c_1776,c_1904,c_1933,c_2108,c_2119,c_2150,c_2275,c_2717,
% 1.75/1.00                 c_2867,c_3409,c_3489]) ).
% 1.75/1.00  
% 1.75/1.00  cnf(c_3549,plain,
% 1.75/1.00      ( $false ),
% 1.75/1.00      inference(superposition,[status(thm)],[c_1619,c_3542]) ).
% 1.75/1.00  
% 1.75/1.00  
% 1.75/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.75/1.00  
% 1.75/1.00  ------                               Statistics
% 1.75/1.00  
% 1.75/1.00  ------ General
% 1.75/1.00  
% 1.75/1.00  abstr_ref_over_cycles:                  0
% 1.75/1.00  abstr_ref_under_cycles:                 0
% 1.75/1.00  gc_basic_clause_elim:                   0
% 1.75/1.00  forced_gc_time:                         0
% 1.75/1.00  parsing_time:                           0.015
% 1.75/1.00  unif_index_cands_time:                  0.
% 1.75/1.00  unif_index_add_time:                    0.
% 1.75/1.00  orderings_time:                         0.
% 1.75/1.00  out_proof_time:                         0.016
% 1.75/1.00  total_time:                             0.136
% 1.75/1.00  num_of_symbols:                         54
% 1.75/1.00  num_of_terms:                           1641
% 1.75/1.00  
% 1.75/1.00  ------ Preprocessing
% 1.75/1.00  
% 1.75/1.00  num_of_splits:                          0
% 1.75/1.00  num_of_split_atoms:                     0
% 1.75/1.00  num_of_reused_defs:                     0
% 1.75/1.00  num_eq_ax_congr_red:                    18
% 1.75/1.00  num_of_sem_filtered_clauses:            1
% 1.75/1.00  num_of_subtypes:                        0
% 1.75/1.00  monotx_restored_types:                  0
% 1.75/1.00  sat_num_of_epr_types:                   0
% 1.75/1.00  sat_num_of_non_cyclic_types:            0
% 1.75/1.00  sat_guarded_non_collapsed_types:        0
% 1.75/1.00  num_pure_diseq_elim:                    0
% 1.75/1.00  simp_replaced_by:                       0
% 1.75/1.00  res_preprocessed:                       100
% 1.75/1.00  prep_upred:                             0
% 1.75/1.00  prep_unflattend:                        35
% 1.75/1.00  smt_new_axioms:                         0
% 1.75/1.00  pred_elim_cands:                        6
% 1.75/1.00  pred_elim:                              8
% 1.75/1.00  pred_elim_cl:                           9
% 1.75/1.00  pred_elim_cycles:                       12
% 1.75/1.00  merged_defs:                            2
% 1.75/1.00  merged_defs_ncl:                        0
% 1.75/1.00  bin_hyper_res:                          2
% 1.75/1.00  prep_cycles:                            4
% 1.75/1.00  pred_elim_time:                         0.015
% 1.75/1.00  splitting_time:                         0.
% 1.75/1.00  sem_filter_time:                        0.
% 1.75/1.00  monotx_time:                            0.
% 1.75/1.00  subtype_inf_time:                       0.
% 1.75/1.00  
% 1.75/1.00  ------ Problem properties
% 1.75/1.00  
% 1.75/1.00  clauses:                                18
% 1.75/1.00  conjectures:                            2
% 1.75/1.00  epr:                                    12
% 1.75/1.00  horn:                                   14
% 1.75/1.00  ground:                                 5
% 1.75/1.00  unary:                                  4
% 1.75/1.00  binary:                                 5
% 1.75/1.00  lits:                                   46
% 1.75/1.00  lits_eq:                                6
% 1.75/1.00  fd_pure:                                0
% 1.75/1.00  fd_pseudo:                              0
% 1.75/1.00  fd_cond:                                1
% 1.75/1.00  fd_pseudo_cond:                         3
% 1.75/1.00  ac_symbols:                             0
% 1.75/1.00  
% 1.75/1.00  ------ Propositional Solver
% 1.75/1.00  
% 1.75/1.00  prop_solver_calls:                      28
% 1.75/1.00  prop_fast_solver_calls:                 913
% 1.75/1.00  smt_solver_calls:                       0
% 1.75/1.00  smt_fast_solver_calls:                  0
% 1.75/1.00  prop_num_of_clauses:                    980
% 1.75/1.00  prop_preprocess_simplified:             4098
% 1.75/1.00  prop_fo_subsumed:                       37
% 1.75/1.00  prop_solver_time:                       0.
% 1.75/1.00  smt_solver_time:                        0.
% 1.75/1.00  smt_fast_solver_time:                   0.
% 1.75/1.00  prop_fast_solver_time:                  0.
% 1.75/1.00  prop_unsat_core_time:                   0.
% 1.75/1.00  
% 1.75/1.00  ------ QBF
% 1.75/1.00  
% 1.75/1.00  qbf_q_res:                              0
% 1.75/1.00  qbf_num_tautologies:                    0
% 1.75/1.00  qbf_prep_cycles:                        0
% 1.75/1.00  
% 1.75/1.00  ------ BMC1
% 1.75/1.00  
% 1.75/1.00  bmc1_current_bound:                     -1
% 1.75/1.00  bmc1_last_solved_bound:                 -1
% 1.75/1.00  bmc1_unsat_core_size:                   -1
% 1.75/1.00  bmc1_unsat_core_parents_size:           -1
% 1.75/1.00  bmc1_merge_next_fun:                    0
% 1.75/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.75/1.00  
% 1.75/1.00  ------ Instantiation
% 1.75/1.00  
% 1.75/1.00  inst_num_of_clauses:                    268
% 1.75/1.00  inst_num_in_passive:                    54
% 1.75/1.00  inst_num_in_active:                     197
% 1.75/1.00  inst_num_in_unprocessed:                17
% 1.75/1.00  inst_num_of_loops:                      210
% 1.75/1.00  inst_num_of_learning_restarts:          0
% 1.75/1.00  inst_num_moves_active_passive:          9
% 1.75/1.00  inst_lit_activity:                      0
% 1.75/1.00  inst_lit_activity_moves:                0
% 1.75/1.00  inst_num_tautologies:                   0
% 1.75/1.00  inst_num_prop_implied:                  0
% 1.75/1.00  inst_num_existing_simplified:           0
% 1.75/1.00  inst_num_eq_res_simplified:             0
% 1.75/1.00  inst_num_child_elim:                    0
% 1.75/1.00  inst_num_of_dismatching_blockings:      10
% 1.75/1.00  inst_num_of_non_proper_insts:           334
% 1.75/1.00  inst_num_of_duplicates:                 0
% 1.75/1.00  inst_inst_num_from_inst_to_res:         0
% 1.75/1.00  inst_dismatching_checking_time:         0.
% 1.75/1.00  
% 1.75/1.00  ------ Resolution
% 1.75/1.00  
% 1.75/1.00  res_num_of_clauses:                     0
% 1.75/1.00  res_num_in_passive:                     0
% 1.75/1.00  res_num_in_active:                      0
% 1.75/1.00  res_num_of_loops:                       104
% 1.75/1.00  res_forward_subset_subsumed:            38
% 1.75/1.00  res_backward_subset_subsumed:           2
% 1.75/1.00  res_forward_subsumed:                   0
% 1.75/1.00  res_backward_subsumed:                  0
% 1.75/1.00  res_forward_subsumption_resolution:     0
% 1.75/1.00  res_backward_subsumption_resolution:    0
% 1.75/1.00  res_clause_to_clause_subsumption:       120
% 1.75/1.00  res_orphan_elimination:                 0
% 1.75/1.00  res_tautology_del:                      44
% 1.75/1.00  res_num_eq_res_simplified:              4
% 1.75/1.00  res_num_sel_changes:                    0
% 1.75/1.00  res_moves_from_active_to_pass:          0
% 1.75/1.00  
% 1.75/1.00  ------ Superposition
% 1.75/1.00  
% 1.75/1.00  sup_time_total:                         0.
% 1.75/1.00  sup_time_generating:                    0.
% 1.75/1.00  sup_time_sim_full:                      0.
% 1.75/1.00  sup_time_sim_immed:                     0.
% 1.75/1.00  
% 1.75/1.00  sup_num_of_clauses:                     32
% 1.75/1.00  sup_num_in_active:                      24
% 1.75/1.00  sup_num_in_passive:                     8
% 1.75/1.00  sup_num_of_loops:                       40
% 1.75/1.00  sup_fw_superposition:                   26
% 1.75/1.00  sup_bw_superposition:                   17
% 1.75/1.00  sup_immediate_simplified:               6
% 1.75/1.00  sup_given_eliminated:                   0
% 1.75/1.00  comparisons_done:                       0
% 1.75/1.00  comparisons_avoided:                    0
% 1.75/1.00  
% 1.75/1.00  ------ Simplifications
% 1.75/1.00  
% 1.75/1.00  
% 1.75/1.00  sim_fw_subset_subsumed:                 3
% 1.75/1.00  sim_bw_subset_subsumed:                 7
% 1.75/1.00  sim_fw_subsumed:                        2
% 1.75/1.00  sim_bw_subsumed:                        0
% 1.75/1.00  sim_fw_subsumption_res:                 1
% 1.75/1.00  sim_bw_subsumption_res:                 0
% 1.75/1.00  sim_tautology_del:                      0
% 1.75/1.00  sim_eq_tautology_del:                   4
% 1.75/1.00  sim_eq_res_simp:                        0
% 1.75/1.00  sim_fw_demodulated:                     1
% 1.75/1.00  sim_bw_demodulated:                     12
% 1.75/1.00  sim_light_normalised:                   1
% 1.75/1.00  sim_joinable_taut:                      0
% 1.75/1.00  sim_joinable_simp:                      0
% 1.75/1.00  sim_ac_normalised:                      0
% 1.75/1.00  sim_smt_subsumption:                    0
% 1.75/1.00  
%------------------------------------------------------------------------------

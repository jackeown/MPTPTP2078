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
% DateTime   : Thu Dec  3 12:12:49 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  185 (2090 expanded)
%              Number of clauses        :  106 ( 444 expanded)
%              Number of leaves         :   21 ( 660 expanded)
%              Depth                    :   26
%              Number of atoms          :  838 (19018 expanded)
%              Number of equality atoms :  265 ( 763 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
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
    inference(negated_conjecture,[],[f28])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f56])).

fof(f68,plain,(
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
    inference(flattening,[],[f67])).

fof(f72,plain,(
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

fof(f71,plain,(
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

fof(f70,plain,(
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

fof(f69,plain,
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

fof(f73,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f68,f72,f71,f70,f69])).

fof(f117,plain,(
    m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f73])).

fof(f116,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f73])).

fof(f23,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(pure_predicate_removal,[],[f23])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f111,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

fof(f112,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f73])).

fof(f113,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f73])).

fof(f114,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f73])).

fof(f115,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f73])).

fof(f25,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f107,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f119,plain,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f118,plain,(
    m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f73])).

fof(f24,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f120,plain,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f27,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f54])).

fof(f110,plain,(
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
    inference(cnf_transformation,[],[f66])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f77,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f108,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f21,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f64])).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_39,negated_conjecture,
    ( m2_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1777,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_40,negated_conjecture,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1776,plain,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_30,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1785,plain,
    ( m2_orders_2(X0,X1,X2) != iProver_top
    | m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7897,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1785])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_46,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_47,plain,
    ( v3_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_48,plain,
    ( v4_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_49,plain,
    ( v5_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_50,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_8317,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7897,c_46,c_47,c_48,c_49,c_50])).

cnf(c_8318,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8317])).

cnf(c_32,plain,
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
    inference(cnf_transformation,[],[f107])).

cnf(c_29,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_29])).

cnf(c_457,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X2,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_1769,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,X2,X0) != iProver_top
    | m1_orders_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v3_orders_2(X2) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_8329,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8318,c_1769])).

cnf(c_12751,plain,
    ( m1_orders_2(X1,sK1,X0) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8329,c_46,c_47,c_48,c_49,c_50])).

cnf(c_12752,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12751])).

cnf(c_12761,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(X0,sK1,sK3) != iProver_top
    | m1_orders_2(sK3,sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_12752])).

cnf(c_51,plain,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_52,plain,
    ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2218,plain,
    ( ~ m2_orders_2(X0,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2441,plain,
    ( ~ m2_orders_2(sK3,sK1,sK2)
    | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_2218])).

cnf(c_2442,plain,
    ( m2_orders_2(sK3,sK1,sK2) != iProver_top
    | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2441])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3037,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_4678,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3037])).

cnf(c_4679,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4678])).

cnf(c_37,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4)
    | r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1779,plain,
    ( m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1778,plain,
    ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_31,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1784,plain,
    ( m1_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8328,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8318,c_1784])).

cnf(c_9543,plain,
    ( r1_tarski(X1,X0) = iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8328,c_46,c_47,c_48,c_49,c_50])).

cnf(c_9544,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) != iProver_top
    | r1_tarski(X1,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9543])).

cnf(c_9550,plain,
    ( m1_orders_2(X0,sK1,sK4) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_9544])).

cnf(c_10066,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_9550])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3038,plain,
    ( r1_tarski(sK3,X0)
    | ~ r2_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6638,plain,
    ( r1_tarski(sK3,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3038])).

cnf(c_6639,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_xboole_0(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6638])).

cnf(c_10270,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10066,c_6639])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1805,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10275,plain,
    ( sK4 = sK3
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10270,c_1805])).

cnf(c_36,negated_conjecture,
    ( ~ m1_orders_2(sK3,sK1,sK4)
    | ~ r2_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_55,plain,
    ( m1_orders_2(sK3,sK1,sK4) != iProver_top
    | r2_xboole_0(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,plain,
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
    inference(cnf_transformation,[],[f110])).

cnf(c_1782,plain,
    ( X0 = X1
    | m2_orders_2(X1,X2,X3) != iProver_top
    | m2_orders_2(X0,X2,X3) != iProver_top
    | m1_orders_2(X0,X2,X1) = iProver_top
    | m1_orders_2(X1,X2,X0) = iProver_top
    | m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v3_orders_2(X2) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4592,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1782])).

cnf(c_5054,plain,
    ( m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4592,c_46,c_47,c_48,c_49,c_50])).

cnf(c_5055,plain,
    ( X0 = X1
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,X1) = iProver_top
    | m1_orders_2(X1,sK1,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5054])).

cnf(c_5063,plain,
    ( sK4 = X0
    | m2_orders_2(X0,sK1,sK2) != iProver_top
    | m1_orders_2(X0,sK1,sK4) = iProver_top
    | m1_orders_2(sK4,sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_5055])).

cnf(c_5093,plain,
    ( sK4 = sK3
    | m1_orders_2(sK4,sK1,sK3) = iProver_top
    | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_5063])).

cnf(c_9551,plain,
    ( m1_orders_2(X0,sK1,sK3) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_9544])).

cnf(c_10071,plain,
    ( sK4 = sK3
    | m1_orders_2(sK3,sK1,sK4) = iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5093,c_9551])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1809,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10276,plain,
    ( sK4 = sK3
    | r2_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_10270,c_1809])).

cnf(c_10288,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10275,c_55,c_10071,c_10276])).

cnf(c_10302,plain,
    ( m1_orders_2(sK3,sK1,sK3) = iProver_top
    | r2_xboole_0(sK3,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10288,c_1779])).

cnf(c_3,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1808,plain,
    ( r2_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10578,plain,
    ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10302,c_1808])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1793,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4705,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X0,X1,X2) != iProver_top
    | m1_orders_2(X2,X1,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_1769])).

cnf(c_10591,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(sK3,sK1,sK3) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10578,c_4705])).

cnf(c_13231,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12761,c_46,c_47,c_48,c_49,c_50,c_51,c_52,c_2442,c_4679,c_10578,c_10591])).

cnf(c_33,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X0,X3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1783,plain,
    ( m2_orders_2(X0,X1,X2) != iProver_top
    | m2_orders_2(X3,X1,X2) != iProver_top
    | m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) != iProver_top
    | r1_xboole_0(X0,X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5706,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1783])).

cnf(c_6090,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | m2_orders_2(X0,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5706,c_46,c_47,c_48,c_49,c_50])).

cnf(c_6091,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | m2_orders_2(X1,sK1,sK2) != iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6090])).

cnf(c_6100,plain,
    ( m2_orders_2(X0,sK1,sK2) != iProver_top
    | r1_xboole_0(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_6091])).

cnf(c_6647,plain,
    ( r1_xboole_0(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_6100])).

cnf(c_13245,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13231,c_6647])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1801,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1803,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5714,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_1803])).

cnf(c_7342,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5714,c_1803])).

cnf(c_28,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1787,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1790,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4464,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1787,c_1790])).

cnf(c_7343,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5714,c_4464])).

cnf(c_7361,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7342,c_7343])).

cnf(c_7459,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7361,c_4464])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1800,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7514,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7459,c_1800])).

cnf(c_13741,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13245,c_7514])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:51:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.39/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/1.00  
% 3.39/1.00  ------  iProver source info
% 3.39/1.00  
% 3.39/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.39/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/1.00  git: non_committed_changes: false
% 3.39/1.00  git: last_make_outside_of_git: false
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  ------ Parsing...
% 3.39/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.00  ------ Proving...
% 3.39/1.00  ------ Problem Properties 
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  clauses                                 44
% 3.39/1.00  conjectures                             10
% 3.39/1.00  EPR                                     19
% 3.39/1.00  Horn                                    34
% 3.39/1.00  unary                                   16
% 3.39/1.00  binary                                  13
% 3.39/1.00  lits                                    130
% 3.39/1.00  lits eq                                 15
% 3.39/1.00  fd_pure                                 0
% 3.39/1.00  fd_pseudo                               0
% 3.39/1.00  fd_cond                                 4
% 3.39/1.00  fd_pseudo_cond                          4
% 3.39/1.00  AC symbols                              0
% 3.39/1.00  
% 3.39/1.00  ------ Input Options Time Limit: Unbounded
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  Current options:
% 3.39/1.00  ------ 
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ Proving...
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS status Theorem for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00   Resolution empty clause
% 3.39/1.00  
% 3.39/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  fof(f28,conjecture,(
% 3.39/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f29,negated_conjecture,(
% 3.39/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 3.39/1.00    inference(negated_conjecture,[],[f28])).
% 3.39/1.00  
% 3.39/1.00  fof(f55,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f29])).
% 3.39/1.00  
% 3.39/1.00  fof(f56,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.39/1.00    inference(flattening,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f67,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.39/1.00    inference(nnf_transformation,[],[f56])).
% 3.39/1.00  
% 3.39/1.00  fof(f68,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.39/1.00    inference(flattening,[],[f67])).
% 3.39/1.00  
% 3.39/1.00  fof(f72,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) => ((~m1_orders_2(X2,X0,sK4) | ~r2_xboole_0(X2,sK4)) & (m1_orders_2(X2,X0,sK4) | r2_xboole_0(X2,sK4)) & m2_orders_2(sK4,X0,X1))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f71,plain,(
% 3.39/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) => (? [X3] : ((~m1_orders_2(sK3,X0,X3) | ~r2_xboole_0(sK3,X3)) & (m1_orders_2(sK3,X0,X3) | r2_xboole_0(sK3,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(sK3,X0,X1))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f70,plain,(
% 3.39/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,sK2)) & m2_orders_2(X2,X0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(X0))))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f69,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK1,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK1,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK1,X1)) & m2_orders_2(X2,sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f73,plain,(
% 3.39/1.00    ((((~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)) & (m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)) & m2_orders_2(sK4,sK1,sK2)) & m2_orders_2(sK3,sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f68,f72,f71,f70,f69])).
% 3.39/1.00  
% 3.39/1.00  fof(f117,plain,(
% 3.39/1.00    m2_orders_2(sK3,sK1,sK2)),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f116,plain,(
% 3.39/1.00    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f23,axiom,(
% 3.39/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f31,plain,(
% 3.39/1.00    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.39/1.00    inference(pure_predicate_removal,[],[f23])).
% 3.39/1.00  
% 3.39/1.00  fof(f45,plain,(
% 3.39/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f31])).
% 3.39/1.00  
% 3.39/1.00  fof(f46,plain,(
% 3.39/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.39/1.00    inference(flattening,[],[f45])).
% 3.39/1.00  
% 3.39/1.00  fof(f105,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f46])).
% 3.39/1.00  
% 3.39/1.00  fof(f111,plain,(
% 3.39/1.00    ~v2_struct_0(sK1)),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f112,plain,(
% 3.39/1.00    v3_orders_2(sK1)),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f113,plain,(
% 3.39/1.00    v4_orders_2(sK1)),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f114,plain,(
% 3.39/1.00    v5_orders_2(sK1)),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f115,plain,(
% 3.39/1.00    l1_orders_2(sK1)),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f25,axiom,(
% 3.39/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f49,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f25])).
% 3.39/1.00  
% 3.39/1.00  fof(f50,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.39/1.00    inference(flattening,[],[f49])).
% 3.39/1.00  
% 3.39/1.00  fof(f107,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f50])).
% 3.39/1.00  
% 3.39/1.00  fof(f22,axiom,(
% 3.39/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f43,plain,(
% 3.39/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f22])).
% 3.39/1.00  
% 3.39/1.00  fof(f44,plain,(
% 3.39/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.39/1.00    inference(flattening,[],[f43])).
% 3.39/1.00  
% 3.39/1.00  fof(f104,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f44])).
% 3.39/1.00  
% 3.39/1.00  fof(f17,axiom,(
% 3.39/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f63,plain,(
% 3.39/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.39/1.00    inference(nnf_transformation,[],[f17])).
% 3.39/1.00  
% 3.39/1.00  fof(f96,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f63])).
% 3.39/1.00  
% 3.39/1.00  fof(f119,plain,(
% 3.39/1.00    m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4)),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f118,plain,(
% 3.39/1.00    m2_orders_2(sK4,sK1,sK2)),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f24,axiom,(
% 3.39/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f47,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f24])).
% 3.39/1.00  
% 3.39/1.00  fof(f48,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.39/1.00    inference(flattening,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f106,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f48])).
% 3.39/1.00  
% 3.39/1.00  fof(f1,axiom,(
% 3.39/1.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f57,plain,(
% 3.39/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 3.39/1.00    inference(nnf_transformation,[],[f1])).
% 3.39/1.00  
% 3.39/1.00  fof(f58,plain,(
% 3.39/1.00    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 3.39/1.00    inference(flattening,[],[f57])).
% 3.39/1.00  
% 3.39/1.00  fof(f74,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f58])).
% 3.39/1.00  
% 3.39/1.00  fof(f4,axiom,(
% 3.39/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f59,plain,(
% 3.39/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.39/1.00    inference(nnf_transformation,[],[f4])).
% 3.39/1.00  
% 3.39/1.00  fof(f60,plain,(
% 3.39/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.39/1.00    inference(flattening,[],[f59])).
% 3.39/1.00  
% 3.39/1.00  fof(f81,plain,(
% 3.39/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f60])).
% 3.39/1.00  
% 3.39/1.00  fof(f120,plain,(
% 3.39/1.00    ~m1_orders_2(sK3,sK1,sK4) | ~r2_xboole_0(sK3,sK4)),
% 3.39/1.00    inference(cnf_transformation,[],[f73])).
% 3.39/1.00  
% 3.39/1.00  fof(f27,axiom,(
% 3.39/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f53,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f54,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.39/1.00    inference(flattening,[],[f53])).
% 3.39/1.00  
% 3.39/1.00  fof(f66,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.39/1.00    inference(nnf_transformation,[],[f54])).
% 3.39/1.00  
% 3.39/1.00  fof(f110,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f66])).
% 3.39/1.00  
% 3.39/1.00  fof(f76,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f58])).
% 3.39/1.00  
% 3.39/1.00  fof(f2,axiom,(
% 3.39/1.00    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f30,plain,(
% 3.39/1.00    ! [X0] : ~r2_xboole_0(X0,X0)),
% 3.39/1.00    inference(rectify,[],[f2])).
% 3.39/1.00  
% 3.39/1.00  fof(f77,plain,(
% 3.39/1.00    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f30])).
% 3.39/1.00  
% 3.39/1.00  fof(f97,plain,(
% 3.39/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f63])).
% 3.39/1.00  
% 3.39/1.00  fof(f26,axiom,(
% 3.39/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f51,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f26])).
% 3.39/1.00  
% 3.39/1.00  fof(f52,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.39/1.00    inference(flattening,[],[f51])).
% 3.39/1.00  
% 3.39/1.00  fof(f108,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f52])).
% 3.39/1.00  
% 3.39/1.00  fof(f7,axiom,(
% 3.39/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f84,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f7])).
% 3.39/1.00  
% 3.39/1.00  fof(f5,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f33,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.39/1.00    inference(ennf_transformation,[],[f5])).
% 3.39/1.00  
% 3.39/1.00  fof(f82,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f33])).
% 3.39/1.00  
% 3.39/1.00  fof(f21,axiom,(
% 3.39/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f42,plain,(
% 3.39/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.39/1.00    inference(ennf_transformation,[],[f21])).
% 3.39/1.00  
% 3.39/1.00  fof(f64,plain,(
% 3.39/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f65,plain,(
% 3.39/1.00    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f64])).
% 3.39/1.00  
% 3.39/1.00  fof(f101,plain,(
% 3.39/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.39/1.00    inference(cnf_transformation,[],[f65])).
% 3.39/1.00  
% 3.39/1.00  fof(f20,axiom,(
% 3.39/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f41,plain,(
% 3.39/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.39/1.00    inference(ennf_transformation,[],[f20])).
% 3.39/1.00  
% 3.39/1.00  fof(f100,plain,(
% 3.39/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f41])).
% 3.39/1.00  
% 3.39/1.00  fof(f8,axiom,(
% 3.39/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f61,plain,(
% 3.39/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.39/1.00    inference(nnf_transformation,[],[f8])).
% 3.39/1.00  
% 3.39/1.00  fof(f86,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.39/1.00    inference(cnf_transformation,[],[f61])).
% 3.39/1.00  
% 3.39/1.00  cnf(c_39,negated_conjecture,
% 3.39/1.00      ( m2_orders_2(sK3,sK1,sK2) ),
% 3.39/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1777,plain,
% 3.39/1.00      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_40,negated_conjecture,
% 3.39/1.00      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1776,plain,
% 3.39/1.00      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_30,plain,
% 3.39/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.39/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | v2_struct_0(X1)
% 3.39/1.00      | ~ v3_orders_2(X1)
% 3.39/1.00      | ~ v4_orders_2(X1)
% 3.39/1.00      | ~ v5_orders_2(X1)
% 3.39/1.00      | ~ l1_orders_2(X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1785,plain,
% 3.39/1.00      ( m2_orders_2(X0,X1,X2) != iProver_top
% 3.39/1.00      | m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) != iProver_top
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.39/1.00      | v2_struct_0(X1) = iProver_top
% 3.39/1.00      | v3_orders_2(X1) != iProver_top
% 3.39/1.00      | v4_orders_2(X1) != iProver_top
% 3.39/1.00      | v5_orders_2(X1) != iProver_top
% 3.39/1.00      | l1_orders_2(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7897,plain,
% 3.39/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.39/1.00      | v2_struct_0(sK1) = iProver_top
% 3.39/1.00      | v3_orders_2(sK1) != iProver_top
% 3.39/1.00      | v4_orders_2(sK1) != iProver_top
% 3.39/1.00      | v5_orders_2(sK1) != iProver_top
% 3.39/1.00      | l1_orders_2(sK1) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1776,c_1785]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_45,negated_conjecture,
% 3.39/1.00      ( ~ v2_struct_0(sK1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_46,plain,
% 3.39/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_44,negated_conjecture,
% 3.39/1.00      ( v3_orders_2(sK1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_47,plain,
% 3.39/1.00      ( v3_orders_2(sK1) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_43,negated_conjecture,
% 3.39/1.00      ( v4_orders_2(sK1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_48,plain,
% 3.39/1.00      ( v4_orders_2(sK1) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_42,negated_conjecture,
% 3.39/1.00      ( v5_orders_2(sK1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_49,plain,
% 3.39/1.00      ( v5_orders_2(sK1) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_41,negated_conjecture,
% 3.39/1.00      ( l1_orders_2(sK1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_50,plain,
% 3.39/1.00      ( l1_orders_2(sK1) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8317,plain,
% 3.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_7897,c_46,c_47,c_48,c_49,c_50]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8318,plain,
% 3.39/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_8317]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_32,plain,
% 3.39/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.39/1.00      | ~ m1_orders_2(X2,X1,X0)
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | v2_struct_0(X1)
% 3.39/1.00      | ~ v3_orders_2(X1)
% 3.39/1.00      | ~ v4_orders_2(X1)
% 3.39/1.00      | ~ v5_orders_2(X1)
% 3.39/1.00      | ~ l1_orders_2(X1)
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_29,plain,
% 3.39/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | v2_struct_0(X1)
% 3.39/1.00      | ~ v3_orders_2(X1)
% 3.39/1.00      | ~ v4_orders_2(X1)
% 3.39/1.00      | ~ v5_orders_2(X1)
% 3.39/1.00      | ~ l1_orders_2(X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_456,plain,
% 3.39/1.00      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | ~ m1_orders_2(X2,X1,X0)
% 3.39/1.00      | ~ m1_orders_2(X0,X1,X2)
% 3.39/1.00      | v2_struct_0(X1)
% 3.39/1.00      | ~ v3_orders_2(X1)
% 3.39/1.00      | ~ v4_orders_2(X1)
% 3.39/1.00      | ~ v5_orders_2(X1)
% 3.39/1.00      | ~ l1_orders_2(X1)
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(global_propositional_subsumption,[status(thm)],[c_32,c_29]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_457,plain,
% 3.39/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.39/1.00      | ~ m1_orders_2(X2,X1,X0)
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | v2_struct_0(X1)
% 3.39/1.00      | ~ v3_orders_2(X1)
% 3.39/1.00      | ~ v4_orders_2(X1)
% 3.39/1.00      | ~ v5_orders_2(X1)
% 3.39/1.00      | ~ l1_orders_2(X1)
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_456]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1769,plain,
% 3.39/1.00      ( k1_xboole_0 = X0
% 3.39/1.00      | m1_orders_2(X1,X2,X0) != iProver_top
% 3.39/1.00      | m1_orders_2(X0,X2,X1) != iProver_top
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.39/1.00      | v2_struct_0(X2) = iProver_top
% 3.39/1.00      | v3_orders_2(X2) != iProver_top
% 3.39/1.00      | v4_orders_2(X2) != iProver_top
% 3.39/1.00      | v5_orders_2(X2) != iProver_top
% 3.39/1.00      | l1_orders_2(X2) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8329,plain,
% 3.39/1.00      ( k1_xboole_0 = X0
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_orders_2(X0,sK1,X1) != iProver_top
% 3.39/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top
% 3.39/1.00      | v2_struct_0(sK1) = iProver_top
% 3.39/1.00      | v3_orders_2(sK1) != iProver_top
% 3.39/1.00      | v4_orders_2(sK1) != iProver_top
% 3.39/1.00      | v5_orders_2(sK1) != iProver_top
% 3.39/1.00      | l1_orders_2(sK1) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_8318,c_1769]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_12751,plain,
% 3.39/1.00      ( m1_orders_2(X1,sK1,X0) != iProver_top
% 3.39/1.00      | m1_orders_2(X0,sK1,X1) != iProver_top
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | k1_xboole_0 = X0 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_8329,c_46,c_47,c_48,c_49,c_50]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_12752,plain,
% 3.39/1.00      ( k1_xboole_0 = X0
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_orders_2(X0,sK1,X1) != iProver_top
% 3.39/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_12751]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_12761,plain,
% 3.39/1.00      ( sK3 = k1_xboole_0
% 3.39/1.00      | m1_orders_2(X0,sK1,sK3) != iProver_top
% 3.39/1.00      | m1_orders_2(sK3,sK1,X0) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1777,c_12752]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_51,plain,
% 3.39/1.00      ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_52,plain,
% 3.39/1.00      ( m2_orders_2(sK3,sK1,sK2) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2218,plain,
% 3.39/1.00      ( ~ m2_orders_2(X0,sK1,sK2)
% 3.39/1.00      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.39/1.00      | v2_struct_0(sK1)
% 3.39/1.00      | ~ v3_orders_2(sK1)
% 3.39/1.00      | ~ v4_orders_2(sK1)
% 3.39/1.00      | ~ v5_orders_2(sK1)
% 3.39/1.00      | ~ l1_orders_2(sK1) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2441,plain,
% 3.39/1.00      ( ~ m2_orders_2(sK3,sK1,sK2)
% 3.39/1.00      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
% 3.39/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.39/1.00      | v2_struct_0(sK1)
% 3.39/1.00      | ~ v3_orders_2(sK1)
% 3.39/1.00      | ~ v4_orders_2(sK1)
% 3.39/1.00      | ~ v5_orders_2(sK1)
% 3.39/1.00      | ~ l1_orders_2(sK1) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_2218]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2442,plain,
% 3.39/1.00      ( m2_orders_2(sK3,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) != iProver_top
% 3.39/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.39/1.00      | v2_struct_0(sK1) = iProver_top
% 3.39/1.00      | v3_orders_2(sK1) != iProver_top
% 3.39/1.00      | v4_orders_2(sK1) != iProver_top
% 3.39/1.00      | v5_orders_2(sK1) != iProver_top
% 3.39/1.00      | l1_orders_2(sK1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_2441]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_22,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3037,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4678,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.39/1.00      | r1_tarski(sK3,u1_struct_0(sK1)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_3037]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4679,plain,
% 3.39/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.39/1.00      | r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_4678]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_37,negated_conjecture,
% 3.39/1.00      ( m1_orders_2(sK3,sK1,sK4) | r2_xboole_0(sK3,sK4) ),
% 3.39/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1779,plain,
% 3.39/1.00      ( m1_orders_2(sK3,sK1,sK4) = iProver_top
% 3.39/1.00      | r2_xboole_0(sK3,sK4) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_38,negated_conjecture,
% 3.39/1.00      ( m2_orders_2(sK4,sK1,sK2) ),
% 3.39/1.00      inference(cnf_transformation,[],[f118]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1778,plain,
% 3.39/1.00      ( m2_orders_2(sK4,sK1,sK2) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_31,plain,
% 3.39/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | r1_tarski(X0,X2)
% 3.39/1.00      | v2_struct_0(X1)
% 3.39/1.00      | ~ v3_orders_2(X1)
% 3.39/1.00      | ~ v4_orders_2(X1)
% 3.39/1.00      | ~ v5_orders_2(X1)
% 3.39/1.00      | ~ l1_orders_2(X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1784,plain,
% 3.39/1.00      ( m1_orders_2(X0,X1,X2) != iProver_top
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.39/1.00      | r1_tarski(X0,X2) = iProver_top
% 3.39/1.00      | v2_struct_0(X1) = iProver_top
% 3.39/1.00      | v3_orders_2(X1) != iProver_top
% 3.39/1.00      | v4_orders_2(X1) != iProver_top
% 3.39/1.00      | v5_orders_2(X1) != iProver_top
% 3.39/1.00      | l1_orders_2(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8328,plain,
% 3.39/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top
% 3.39/1.00      | r1_tarski(X1,X0) = iProver_top
% 3.39/1.00      | v2_struct_0(sK1) = iProver_top
% 3.39/1.00      | v3_orders_2(sK1) != iProver_top
% 3.39/1.00      | v4_orders_2(sK1) != iProver_top
% 3.39/1.00      | v5_orders_2(sK1) != iProver_top
% 3.39/1.00      | l1_orders_2(sK1) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_8318,c_1784]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9543,plain,
% 3.39/1.00      ( r1_tarski(X1,X0) = iProver_top
% 3.39/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_8328,c_46,c_47,c_48,c_49,c_50]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9544,plain,
% 3.39/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_orders_2(X1,sK1,X0) != iProver_top
% 3.39/1.00      | r1_tarski(X1,X0) = iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_9543]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9550,plain,
% 3.39/1.00      ( m1_orders_2(X0,sK1,sK4) != iProver_top
% 3.39/1.00      | r1_tarski(X0,sK4) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1778,c_9544]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10066,plain,
% 3.39/1.00      ( r1_tarski(sK3,sK4) = iProver_top | r2_xboole_0(sK3,sK4) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1779,c_9550]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2,plain,
% 3.39/1.00      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3038,plain,
% 3.39/1.00      ( r1_tarski(sK3,X0) | ~ r2_xboole_0(sK3,X0) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6638,plain,
% 3.39/1.00      ( r1_tarski(sK3,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_3038]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6639,plain,
% 3.39/1.00      ( r1_tarski(sK3,sK4) = iProver_top
% 3.39/1.00      | r2_xboole_0(sK3,sK4) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_6638]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10270,plain,
% 3.39/1.00      ( r1_tarski(sK3,sK4) = iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_10066,c_6639]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1805,plain,
% 3.39/1.00      ( X0 = X1
% 3.39/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.39/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10275,plain,
% 3.39/1.00      ( sK4 = sK3 | r1_tarski(sK4,sK3) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_10270,c_1805]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_36,negated_conjecture,
% 3.39/1.00      ( ~ m1_orders_2(sK3,sK1,sK4) | ~ r2_xboole_0(sK3,sK4) ),
% 3.39/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_55,plain,
% 3.39/1.00      ( m1_orders_2(sK3,sK1,sK4) != iProver_top
% 3.39/1.00      | r2_xboole_0(sK3,sK4) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_34,plain,
% 3.39/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.39/1.00      | ~ m2_orders_2(X3,X1,X2)
% 3.39/1.00      | m1_orders_2(X3,X1,X0)
% 3.39/1.00      | m1_orders_2(X0,X1,X3)
% 3.39/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.39/1.00      | v2_struct_0(X1)
% 3.39/1.00      | ~ v3_orders_2(X1)
% 3.39/1.00      | ~ v4_orders_2(X1)
% 3.39/1.00      | ~ v5_orders_2(X1)
% 3.39/1.00      | ~ l1_orders_2(X1)
% 3.39/1.00      | X3 = X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1782,plain,
% 3.39/1.00      ( X0 = X1
% 3.39/1.00      | m2_orders_2(X1,X2,X3) != iProver_top
% 3.39/1.00      | m2_orders_2(X0,X2,X3) != iProver_top
% 3.39/1.00      | m1_orders_2(X0,X2,X1) = iProver_top
% 3.39/1.00      | m1_orders_2(X1,X2,X0) = iProver_top
% 3.39/1.00      | m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) != iProver_top
% 3.39/1.00      | v2_struct_0(X2) = iProver_top
% 3.39/1.00      | v3_orders_2(X2) != iProver_top
% 3.39/1.00      | v4_orders_2(X2) != iProver_top
% 3.39/1.00      | v5_orders_2(X2) != iProver_top
% 3.39/1.00      | l1_orders_2(X2) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4592,plain,
% 3.39/1.00      ( X0 = X1
% 3.39/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_orders_2(X1,sK1,X0) = iProver_top
% 3.39/1.00      | m1_orders_2(X0,sK1,X1) = iProver_top
% 3.39/1.00      | v2_struct_0(sK1) = iProver_top
% 3.39/1.00      | v3_orders_2(sK1) != iProver_top
% 3.39/1.00      | v4_orders_2(sK1) != iProver_top
% 3.39/1.00      | v5_orders_2(sK1) != iProver_top
% 3.39/1.00      | l1_orders_2(sK1) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1776,c_1782]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5054,plain,
% 3.39/1.00      ( m1_orders_2(X0,sK1,X1) = iProver_top
% 3.39/1.00      | m1_orders_2(X1,sK1,X0) = iProver_top
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 3.39/1.00      | X0 = X1 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_4592,c_46,c_47,c_48,c_49,c_50]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5055,plain,
% 3.39/1.00      ( X0 = X1
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_orders_2(X0,sK1,X1) = iProver_top
% 3.39/1.00      | m1_orders_2(X1,sK1,X0) = iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_5054]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5063,plain,
% 3.39/1.00      ( sK4 = X0
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m1_orders_2(X0,sK1,sK4) = iProver_top
% 3.39/1.00      | m1_orders_2(sK4,sK1,X0) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1778,c_5055]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5093,plain,
% 3.39/1.00      ( sK4 = sK3
% 3.39/1.00      | m1_orders_2(sK4,sK1,sK3) = iProver_top
% 3.39/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1777,c_5063]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9551,plain,
% 3.39/1.00      ( m1_orders_2(X0,sK1,sK3) != iProver_top
% 3.39/1.00      | r1_tarski(X0,sK3) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1777,c_9544]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10071,plain,
% 3.39/1.00      ( sK4 = sK3
% 3.39/1.00      | m1_orders_2(sK3,sK1,sK4) = iProver_top
% 3.39/1.00      | r1_tarski(sK4,sK3) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_5093,c_9551]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_0,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1809,plain,
% 3.39/1.00      ( X0 = X1
% 3.39/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.39/1.00      | r2_xboole_0(X1,X0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10276,plain,
% 3.39/1.00      ( sK4 = sK3 | r2_xboole_0(sK3,sK4) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_10270,c_1809]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10288,plain,
% 3.39/1.00      ( sK4 = sK3 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_10275,c_55,c_10071,c_10276]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10302,plain,
% 3.39/1.00      ( m1_orders_2(sK3,sK1,sK3) = iProver_top
% 3.39/1.00      | r2_xboole_0(sK3,sK3) = iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_10288,c_1779]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3,plain,
% 3.39/1.00      ( ~ r2_xboole_0(X0,X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1808,plain,
% 3.39/1.00      ( r2_xboole_0(X0,X0) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10578,plain,
% 3.39/1.00      ( m1_orders_2(sK3,sK1,sK3) = iProver_top ),
% 3.39/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_10302,c_1808]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_21,plain,
% 3.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1793,plain,
% 3.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.39/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4705,plain,
% 3.39/1.00      ( k1_xboole_0 = X0
% 3.39/1.00      | m1_orders_2(X0,X1,X2) != iProver_top
% 3.39/1.00      | m1_orders_2(X2,X1,X0) != iProver_top
% 3.39/1.00      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 3.39/1.00      | v2_struct_0(X1) = iProver_top
% 3.39/1.00      | v3_orders_2(X1) != iProver_top
% 3.39/1.00      | v4_orders_2(X1) != iProver_top
% 3.39/1.00      | v5_orders_2(X1) != iProver_top
% 3.39/1.00      | l1_orders_2(X1) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1793,c_1769]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10591,plain,
% 3.39/1.00      ( sK3 = k1_xboole_0
% 3.39/1.00      | m1_orders_2(sK3,sK1,sK3) != iProver_top
% 3.39/1.00      | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top
% 3.39/1.00      | v2_struct_0(sK1) = iProver_top
% 3.39/1.00      | v3_orders_2(sK1) != iProver_top
% 3.39/1.00      | v4_orders_2(sK1) != iProver_top
% 3.39/1.00      | v5_orders_2(sK1) != iProver_top
% 3.39/1.00      | l1_orders_2(sK1) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_10578,c_4705]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_13231,plain,
% 3.39/1.00      ( sK3 = k1_xboole_0 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_12761,c_46,c_47,c_48,c_49,c_50,c_51,c_52,c_2442,c_4679,
% 3.39/1.00                 c_10578,c_10591]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_33,plain,
% 3.39/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 3.39/1.00      | ~ m2_orders_2(X3,X1,X2)
% 3.39/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 3.39/1.00      | ~ r1_xboole_0(X0,X3)
% 3.39/1.00      | v2_struct_0(X1)
% 3.39/1.00      | ~ v3_orders_2(X1)
% 3.39/1.00      | ~ v4_orders_2(X1)
% 3.39/1.00      | ~ v5_orders_2(X1)
% 3.39/1.00      | ~ l1_orders_2(X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1783,plain,
% 3.39/1.00      ( m2_orders_2(X0,X1,X2) != iProver_top
% 3.39/1.00      | m2_orders_2(X3,X1,X2) != iProver_top
% 3.39/1.00      | m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) != iProver_top
% 3.39/1.00      | r1_xboole_0(X0,X3) != iProver_top
% 3.39/1.00      | v2_struct_0(X1) = iProver_top
% 3.39/1.00      | v3_orders_2(X1) != iProver_top
% 3.39/1.00      | v4_orders_2(X1) != iProver_top
% 3.39/1.00      | v5_orders_2(X1) != iProver_top
% 3.39/1.00      | l1_orders_2(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5706,plain,
% 3.39/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 3.39/1.00      | r1_xboole_0(X0,X1) != iProver_top
% 3.39/1.00      | v2_struct_0(sK1) = iProver_top
% 3.39/1.00      | v3_orders_2(sK1) != iProver_top
% 3.39/1.00      | v4_orders_2(sK1) != iProver_top
% 3.39/1.00      | v5_orders_2(sK1) != iProver_top
% 3.39/1.00      | l1_orders_2(sK1) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1776,c_1783]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6090,plain,
% 3.39/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.39/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 3.39/1.00      | m2_orders_2(X0,sK1,sK2) != iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_5706,c_46,c_47,c_48,c_49,c_50]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6091,plain,
% 3.39/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | m2_orders_2(X1,sK1,sK2) != iProver_top
% 3.39/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_6090]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6100,plain,
% 3.39/1.00      ( m2_orders_2(X0,sK1,sK2) != iProver_top
% 3.39/1.00      | r1_xboole_0(sK3,X0) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1777,c_6091]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6647,plain,
% 3.39/1.00      ( r1_xboole_0(sK3,sK3) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1777,c_6100]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_13245,plain,
% 3.39/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_13231,c_6647]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10,plain,
% 3.39/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.39/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1801,plain,
% 3.39/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 3.39/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1803,plain,
% 3.39/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 3.39/1.00      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5714,plain,
% 3.39/1.00      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1801,c_1803]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7342,plain,
% 3.39/1.00      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_5714,c_1803]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_28,plain,
% 3.39/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1787,plain,
% 3.39/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_25,plain,
% 3.39/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1790,plain,
% 3.39/1.00      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4464,plain,
% 3.39/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,sK0(X0)) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1787,c_1790]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7343,plain,
% 3.39/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_5714,c_4464]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7361,plain,
% 3.39/1.00      ( r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) = iProver_top ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_7342,c_7343]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7459,plain,
% 3.39/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_7361,c_4464]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_11,plain,
% 3.39/1.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1800,plain,
% 3.39/1.00      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7514,plain,
% 3.39/1.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_7459,c_1800]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_13741,plain,
% 3.39/1.00      ( $false ),
% 3.39/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_13245,c_7514]) ).
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  ------                               Statistics
% 3.39/1.00  
% 3.39/1.00  ------ Selected
% 3.39/1.00  
% 3.39/1.00  total_time:                             0.363
% 3.39/1.00  
%------------------------------------------------------------------------------

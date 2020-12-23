%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:58 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 420 expanded)
%              Number of clauses        :   78 ( 109 expanded)
%              Number of leaves         :   18 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          :  547 (3024 expanded)
%              Number of equality atoms :  121 ( 127 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(rectify,[],[f2])).

fof(f17,plain,(
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

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,conjecture,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f16,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( r1_tsep_1(X3,X2)
            | r1_tsep_1(X2,X3) )
          & ( ~ r1_tsep_1(X3,X1)
            | ~ r1_tsep_1(X1,X3) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0) )
     => ( ( r1_tsep_1(sK5,X2)
          | r1_tsep_1(X2,sK5) )
        & ( ~ r1_tsep_1(sK5,X1)
          | ~ r1_tsep_1(X1,sK5) )
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,X1)
                | ~ r1_tsep_1(X1,X3) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0) )
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ( r1_tsep_1(X3,sK4)
              | r1_tsep_1(sK4,X3) )
            & ( ~ r1_tsep_1(X3,X1)
              | ~ r1_tsep_1(X1,X3) )
            & m1_pre_topc(X1,sK4)
            & m1_pre_topc(X3,X0) )
        & m1_pre_topc(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,sK3)
                  | ~ r1_tsep_1(sK3,X3) )
                & m1_pre_topc(sK3,X2)
                & m1_pre_topc(X3,X0) )
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK2) )
              & m1_pre_topc(X2,sK2) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( r1_tsep_1(sK5,sK4)
      | r1_tsep_1(sK4,sK5) )
    & ( ~ r1_tsep_1(sK5,sK3)
      | ~ r1_tsep_1(sK3,sK5) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & m1_pre_topc(sK4,sK2)
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f42,f41,f40,f39])).

fof(f70,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1152,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1136,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1139,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1732,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1145])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1147,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1148,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1150,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2229,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1150])).

cnf(c_3539,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_2229])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_62,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3986,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3539,c_62])).

cnf(c_3995,plain,
    ( k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_3986])).

cnf(c_8419,plain,
    ( k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) = u1_struct_0(sK4)
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_3995])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1465,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_17,c_26])).

cnf(c_1466,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1465])).

cnf(c_8520,plain,
    ( k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8419,c_29,c_1466])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1156,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8539,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8520,c_1156])).

cnf(c_9228,plain,
    ( r1_xboole_0(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK1(X0,u1_struct_0(sK3)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_8539])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1151,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1141,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1153,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2292,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1153])).

cnf(c_3690,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_xboole_0(u1_struct_0(X1),X2) = iProver_top
    | r2_hidden(sK1(u1_struct_0(X1),X2),u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_2292])).

cnf(c_10329,plain,
    ( r1_tsep_1(sK4,X0) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9228,c_3690])).

cnf(c_10364,plain,
    ( r1_tsep_1(sK4,sK5) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10329])).

cnf(c_20,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2067,plain,
    ( r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2068,plain,
    ( r1_tsep_1(sK3,sK5) = iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2067])).

cnf(c_22,negated_conjecture,
    ( r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1937,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_20,c_22])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_16,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_48,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1368,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1370,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1524,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1465,c_28])).

cnf(c_1752,plain,
    ( l1_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_1524,c_16])).

cnf(c_1138,plain,
    ( r1_tsep_1(sK4,sK5) = iProver_top
    | r1_tsep_1(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1140,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1916,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1140])).

cnf(c_1917,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1916])).

cnf(c_1940,plain,
    ( r1_tsep_1(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1937,c_28,c_25,c_48,c_1370,c_1752,c_1917])).

cnf(c_2048,plain,
    ( r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_1940,c_20])).

cnf(c_2049,plain,
    ( r1_tsep_1(sK4,sK5) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2048])).

cnf(c_18,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1948,plain,
    ( r1_tsep_1(sK5,sK3)
    | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1949,plain,
    ( r1_tsep_1(sK5,sK3) = iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1948])).

cnf(c_1753,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1752])).

cnf(c_1461,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_17,c_24])).

cnf(c_1470,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1461,c_28,c_1465])).

cnf(c_1482,plain,
    ( l1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_1470,c_16])).

cnf(c_1483,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

cnf(c_1369,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1368])).

cnf(c_1371,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_47,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_49,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,plain,
    ( r1_tsep_1(sK3,sK5) != iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_32,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10364,c_2068,c_2049,c_1949,c_1753,c_1483,c_1371,c_49,c_34,c_32,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.04/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/1.00  
% 4.04/1.00  ------  iProver source info
% 4.04/1.00  
% 4.04/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.04/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/1.00  git: non_committed_changes: false
% 4.04/1.00  git: last_make_outside_of_git: false
% 4.04/1.00  
% 4.04/1.00  ------ 
% 4.04/1.00  
% 4.04/1.00  ------ Input Options
% 4.04/1.00  
% 4.04/1.00  --out_options                           all
% 4.04/1.00  --tptp_safe_out                         true
% 4.04/1.00  --problem_path                          ""
% 4.04/1.00  --include_path                          ""
% 4.04/1.00  --clausifier                            res/vclausify_rel
% 4.04/1.00  --clausifier_options                    --mode clausify
% 4.04/1.00  --stdin                                 false
% 4.04/1.00  --stats_out                             sel
% 4.04/1.00  
% 4.04/1.00  ------ General Options
% 4.04/1.00  
% 4.04/1.00  --fof                                   false
% 4.04/1.00  --time_out_real                         604.99
% 4.04/1.00  --time_out_virtual                      -1.
% 4.04/1.00  --symbol_type_check                     false
% 4.04/1.00  --clausify_out                          false
% 4.04/1.00  --sig_cnt_out                           false
% 4.04/1.00  --trig_cnt_out                          false
% 4.04/1.00  --trig_cnt_out_tolerance                1.
% 4.04/1.00  --trig_cnt_out_sk_spl                   false
% 4.04/1.00  --abstr_cl_out                          false
% 4.04/1.00  
% 4.04/1.00  ------ Global Options
% 4.04/1.00  
% 4.04/1.00  --schedule                              none
% 4.04/1.00  --add_important_lit                     false
% 4.04/1.00  --prop_solver_per_cl                    1000
% 4.04/1.00  --min_unsat_core                        false
% 4.04/1.00  --soft_assumptions                      false
% 4.04/1.00  --soft_lemma_size                       3
% 4.04/1.00  --prop_impl_unit_size                   0
% 4.04/1.00  --prop_impl_unit                        []
% 4.04/1.00  --share_sel_clauses                     true
% 4.04/1.00  --reset_solvers                         false
% 4.04/1.00  --bc_imp_inh                            [conj_cone]
% 4.04/1.00  --conj_cone_tolerance                   3.
% 4.04/1.00  --extra_neg_conj                        none
% 4.04/1.00  --large_theory_mode                     true
% 4.04/1.00  --prolific_symb_bound                   200
% 4.04/1.00  --lt_threshold                          2000
% 4.04/1.00  --clause_weak_htbl                      true
% 4.04/1.00  --gc_record_bc_elim                     false
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing Options
% 4.04/1.00  
% 4.04/1.00  --preprocessing_flag                    true
% 4.04/1.00  --time_out_prep_mult                    0.1
% 4.04/1.00  --splitting_mode                        input
% 4.04/1.00  --splitting_grd                         true
% 4.04/1.00  --splitting_cvd                         false
% 4.04/1.00  --splitting_cvd_svl                     false
% 4.04/1.00  --splitting_nvd                         32
% 4.04/1.00  --sub_typing                            true
% 4.04/1.00  --prep_gs_sim                           false
% 4.04/1.00  --prep_unflatten                        true
% 4.04/1.00  --prep_res_sim                          true
% 4.04/1.00  --prep_upred                            true
% 4.04/1.00  --prep_sem_filter                       exhaustive
% 4.04/1.00  --prep_sem_filter_out                   false
% 4.04/1.00  --pred_elim                             false
% 4.04/1.00  --res_sim_input                         true
% 4.04/1.00  --eq_ax_congr_red                       true
% 4.04/1.00  --pure_diseq_elim                       true
% 4.04/1.00  --brand_transform                       false
% 4.04/1.00  --non_eq_to_eq                          false
% 4.04/1.00  --prep_def_merge                        true
% 4.04/1.00  --prep_def_merge_prop_impl              false
% 4.04/1.00  --prep_def_merge_mbd                    true
% 4.04/1.00  --prep_def_merge_tr_red                 false
% 4.04/1.00  --prep_def_merge_tr_cl                  false
% 4.04/1.00  --smt_preprocessing                     true
% 4.04/1.00  --smt_ac_axioms                         fast
% 4.04/1.00  --preprocessed_out                      false
% 4.04/1.00  --preprocessed_stats                    false
% 4.04/1.00  
% 4.04/1.00  ------ Abstraction refinement Options
% 4.04/1.00  
% 4.04/1.00  --abstr_ref                             []
% 4.04/1.00  --abstr_ref_prep                        false
% 4.04/1.00  --abstr_ref_until_sat                   false
% 4.04/1.00  --abstr_ref_sig_restrict                funpre
% 4.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.00  --abstr_ref_under                       []
% 4.04/1.00  
% 4.04/1.00  ------ SAT Options
% 4.04/1.00  
% 4.04/1.00  --sat_mode                              false
% 4.04/1.00  --sat_fm_restart_options                ""
% 4.04/1.00  --sat_gr_def                            false
% 4.04/1.00  --sat_epr_types                         true
% 4.04/1.00  --sat_non_cyclic_types                  false
% 4.04/1.00  --sat_finite_models                     false
% 4.04/1.00  --sat_fm_lemmas                         false
% 4.04/1.00  --sat_fm_prep                           false
% 4.04/1.00  --sat_fm_uc_incr                        true
% 4.04/1.00  --sat_out_model                         small
% 4.04/1.00  --sat_out_clauses                       false
% 4.04/1.00  
% 4.04/1.00  ------ QBF Options
% 4.04/1.00  
% 4.04/1.00  --qbf_mode                              false
% 4.04/1.00  --qbf_elim_univ                         false
% 4.04/1.00  --qbf_dom_inst                          none
% 4.04/1.00  --qbf_dom_pre_inst                      false
% 4.04/1.00  --qbf_sk_in                             false
% 4.04/1.00  --qbf_pred_elim                         true
% 4.04/1.00  --qbf_split                             512
% 4.04/1.00  
% 4.04/1.00  ------ BMC1 Options
% 4.04/1.00  
% 4.04/1.00  --bmc1_incremental                      false
% 4.04/1.00  --bmc1_axioms                           reachable_all
% 4.04/1.00  --bmc1_min_bound                        0
% 4.04/1.00  --bmc1_max_bound                        -1
% 4.04/1.00  --bmc1_max_bound_default                -1
% 4.04/1.00  --bmc1_symbol_reachability              true
% 4.04/1.00  --bmc1_property_lemmas                  false
% 4.04/1.00  --bmc1_k_induction                      false
% 4.04/1.00  --bmc1_non_equiv_states                 false
% 4.04/1.00  --bmc1_deadlock                         false
% 4.04/1.00  --bmc1_ucm                              false
% 4.04/1.00  --bmc1_add_unsat_core                   none
% 4.04/1.00  --bmc1_unsat_core_children              false
% 4.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.00  --bmc1_out_stat                         full
% 4.04/1.00  --bmc1_ground_init                      false
% 4.04/1.00  --bmc1_pre_inst_next_state              false
% 4.04/1.00  --bmc1_pre_inst_state                   false
% 4.04/1.00  --bmc1_pre_inst_reach_state             false
% 4.04/1.00  --bmc1_out_unsat_core                   false
% 4.04/1.00  --bmc1_aig_witness_out                  false
% 4.04/1.00  --bmc1_verbose                          false
% 4.04/1.00  --bmc1_dump_clauses_tptp                false
% 4.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.00  --bmc1_dump_file                        -
% 4.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.00  --bmc1_ucm_extend_mode                  1
% 4.04/1.00  --bmc1_ucm_init_mode                    2
% 4.04/1.00  --bmc1_ucm_cone_mode                    none
% 4.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.00  --bmc1_ucm_relax_model                  4
% 4.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.00  --bmc1_ucm_layered_model                none
% 4.04/1.00  --bmc1_ucm_max_lemma_size               10
% 4.04/1.00  
% 4.04/1.00  ------ AIG Options
% 4.04/1.00  
% 4.04/1.00  --aig_mode                              false
% 4.04/1.00  
% 4.04/1.00  ------ Instantiation Options
% 4.04/1.00  
% 4.04/1.00  --instantiation_flag                    true
% 4.04/1.00  --inst_sos_flag                         false
% 4.04/1.00  --inst_sos_phase                        true
% 4.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel_side                     num_symb
% 4.04/1.00  --inst_solver_per_active                1400
% 4.04/1.00  --inst_solver_calls_frac                1.
% 4.04/1.00  --inst_passive_queue_type               priority_queues
% 4.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.00  --inst_passive_queues_freq              [25;2]
% 4.04/1.00  --inst_dismatching                      true
% 4.04/1.00  --inst_eager_unprocessed_to_passive     true
% 4.04/1.00  --inst_prop_sim_given                   true
% 4.04/1.00  --inst_prop_sim_new                     false
% 4.04/1.00  --inst_subs_new                         false
% 4.04/1.00  --inst_eq_res_simp                      false
% 4.04/1.00  --inst_subs_given                       false
% 4.04/1.00  --inst_orphan_elimination               true
% 4.04/1.00  --inst_learning_loop_flag               true
% 4.04/1.00  --inst_learning_start                   3000
% 4.04/1.00  --inst_learning_factor                  2
% 4.04/1.00  --inst_start_prop_sim_after_learn       3
% 4.04/1.00  --inst_sel_renew                        solver
% 4.04/1.00  --inst_lit_activity_flag                true
% 4.04/1.00  --inst_restr_to_given                   false
% 4.04/1.00  --inst_activity_threshold               500
% 4.04/1.00  --inst_out_proof                        true
% 4.04/1.00  
% 4.04/1.00  ------ Resolution Options
% 4.04/1.00  
% 4.04/1.00  --resolution_flag                       true
% 4.04/1.00  --res_lit_sel                           adaptive
% 4.04/1.00  --res_lit_sel_side                      none
% 4.04/1.00  --res_ordering                          kbo
% 4.04/1.00  --res_to_prop_solver                    active
% 4.04/1.00  --res_prop_simpl_new                    false
% 4.04/1.00  --res_prop_simpl_given                  true
% 4.04/1.00  --res_passive_queue_type                priority_queues
% 4.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.00  --res_passive_queues_freq               [15;5]
% 4.04/1.00  --res_forward_subs                      full
% 4.04/1.00  --res_backward_subs                     full
% 4.04/1.00  --res_forward_subs_resolution           true
% 4.04/1.00  --res_backward_subs_resolution          true
% 4.04/1.00  --res_orphan_elimination                true
% 4.04/1.00  --res_time_limit                        2.
% 4.04/1.00  --res_out_proof                         true
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Options
% 4.04/1.00  
% 4.04/1.00  --superposition_flag                    true
% 4.04/1.00  --sup_passive_queue_type                priority_queues
% 4.04/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.00  --sup_passive_queues_freq               [1;4]
% 4.04/1.00  --demod_completeness_check              fast
% 4.04/1.00  --demod_use_ground                      true
% 4.04/1.00  --sup_to_prop_solver                    passive
% 4.04/1.00  --sup_prop_simpl_new                    true
% 4.04/1.00  --sup_prop_simpl_given                  true
% 4.04/1.00  --sup_fun_splitting                     false
% 4.04/1.00  --sup_smt_interval                      50000
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Simplification Setup
% 4.04/1.00  
% 4.04/1.00  --sup_indices_passive                   []
% 4.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_full_bw                           [BwDemod]
% 4.04/1.00  --sup_immed_triv                        [TrivRules]
% 4.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_immed_bw_main                     []
% 4.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  
% 4.04/1.00  ------ Combination Options
% 4.04/1.00  
% 4.04/1.00  --comb_res_mult                         3
% 4.04/1.00  --comb_sup_mult                         2
% 4.04/1.00  --comb_inst_mult                        10
% 4.04/1.00  
% 4.04/1.00  ------ Debug Options
% 4.04/1.00  
% 4.04/1.00  --dbg_backtrace                         false
% 4.04/1.00  --dbg_dump_prop_clauses                 false
% 4.04/1.00  --dbg_dump_prop_clauses_file            -
% 4.04/1.00  --dbg_out_stat                          false
% 4.04/1.00  ------ Parsing...
% 4.04/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/1.00  ------ Proving...
% 4.04/1.00  ------ Problem Properties 
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  clauses                                 28
% 4.04/1.00  conjectures                             7
% 4.04/1.00  EPR                                     13
% 4.04/1.00  Horn                                    23
% 4.04/1.00  unary                                   7
% 4.04/1.00  binary                                  9
% 4.04/1.00  lits                                    65
% 4.04/1.00  lits eq                                 4
% 4.04/1.00  fd_pure                                 0
% 4.04/1.00  fd_pseudo                               0
% 4.04/1.00  fd_cond                                 0
% 4.04/1.00  fd_pseudo_cond                          4
% 4.04/1.00  AC symbols                              0
% 4.04/1.00  
% 4.04/1.00  ------ Input Options Time Limit: Unbounded
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  ------ 
% 4.04/1.00  Current options:
% 4.04/1.00  ------ 
% 4.04/1.00  
% 4.04/1.00  ------ Input Options
% 4.04/1.00  
% 4.04/1.00  --out_options                           all
% 4.04/1.00  --tptp_safe_out                         true
% 4.04/1.00  --problem_path                          ""
% 4.04/1.00  --include_path                          ""
% 4.04/1.00  --clausifier                            res/vclausify_rel
% 4.04/1.00  --clausifier_options                    --mode clausify
% 4.04/1.00  --stdin                                 false
% 4.04/1.00  --stats_out                             sel
% 4.04/1.00  
% 4.04/1.00  ------ General Options
% 4.04/1.00  
% 4.04/1.00  --fof                                   false
% 4.04/1.00  --time_out_real                         604.99
% 4.04/1.00  --time_out_virtual                      -1.
% 4.04/1.00  --symbol_type_check                     false
% 4.04/1.00  --clausify_out                          false
% 4.04/1.00  --sig_cnt_out                           false
% 4.04/1.00  --trig_cnt_out                          false
% 4.04/1.00  --trig_cnt_out_tolerance                1.
% 4.04/1.00  --trig_cnt_out_sk_spl                   false
% 4.04/1.00  --abstr_cl_out                          false
% 4.04/1.00  
% 4.04/1.00  ------ Global Options
% 4.04/1.00  
% 4.04/1.00  --schedule                              none
% 4.04/1.00  --add_important_lit                     false
% 4.04/1.00  --prop_solver_per_cl                    1000
% 4.04/1.00  --min_unsat_core                        false
% 4.04/1.00  --soft_assumptions                      false
% 4.04/1.00  --soft_lemma_size                       3
% 4.04/1.00  --prop_impl_unit_size                   0
% 4.04/1.00  --prop_impl_unit                        []
% 4.04/1.00  --share_sel_clauses                     true
% 4.04/1.00  --reset_solvers                         false
% 4.04/1.00  --bc_imp_inh                            [conj_cone]
% 4.04/1.00  --conj_cone_tolerance                   3.
% 4.04/1.00  --extra_neg_conj                        none
% 4.04/1.00  --large_theory_mode                     true
% 4.04/1.00  --prolific_symb_bound                   200
% 4.04/1.00  --lt_threshold                          2000
% 4.04/1.00  --clause_weak_htbl                      true
% 4.04/1.00  --gc_record_bc_elim                     false
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing Options
% 4.04/1.00  
% 4.04/1.00  --preprocessing_flag                    true
% 4.04/1.00  --time_out_prep_mult                    0.1
% 4.04/1.00  --splitting_mode                        input
% 4.04/1.00  --splitting_grd                         true
% 4.04/1.00  --splitting_cvd                         false
% 4.04/1.00  --splitting_cvd_svl                     false
% 4.04/1.00  --splitting_nvd                         32
% 4.04/1.00  --sub_typing                            true
% 4.04/1.00  --prep_gs_sim                           false
% 4.04/1.00  --prep_unflatten                        true
% 4.04/1.00  --prep_res_sim                          true
% 4.04/1.00  --prep_upred                            true
% 4.04/1.00  --prep_sem_filter                       exhaustive
% 4.04/1.00  --prep_sem_filter_out                   false
% 4.04/1.00  --pred_elim                             false
% 4.04/1.00  --res_sim_input                         true
% 4.04/1.00  --eq_ax_congr_red                       true
% 4.04/1.00  --pure_diseq_elim                       true
% 4.04/1.00  --brand_transform                       false
% 4.04/1.00  --non_eq_to_eq                          false
% 4.04/1.00  --prep_def_merge                        true
% 4.04/1.00  --prep_def_merge_prop_impl              false
% 4.04/1.00  --prep_def_merge_mbd                    true
% 4.04/1.00  --prep_def_merge_tr_red                 false
% 4.04/1.00  --prep_def_merge_tr_cl                  false
% 4.04/1.00  --smt_preprocessing                     true
% 4.04/1.00  --smt_ac_axioms                         fast
% 4.04/1.00  --preprocessed_out                      false
% 4.04/1.00  --preprocessed_stats                    false
% 4.04/1.00  
% 4.04/1.00  ------ Abstraction refinement Options
% 4.04/1.00  
% 4.04/1.00  --abstr_ref                             []
% 4.04/1.00  --abstr_ref_prep                        false
% 4.04/1.00  --abstr_ref_until_sat                   false
% 4.04/1.00  --abstr_ref_sig_restrict                funpre
% 4.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.00  --abstr_ref_under                       []
% 4.04/1.00  
% 4.04/1.00  ------ SAT Options
% 4.04/1.00  
% 4.04/1.00  --sat_mode                              false
% 4.04/1.00  --sat_fm_restart_options                ""
% 4.04/1.00  --sat_gr_def                            false
% 4.04/1.00  --sat_epr_types                         true
% 4.04/1.00  --sat_non_cyclic_types                  false
% 4.04/1.00  --sat_finite_models                     false
% 4.04/1.00  --sat_fm_lemmas                         false
% 4.04/1.00  --sat_fm_prep                           false
% 4.04/1.00  --sat_fm_uc_incr                        true
% 4.04/1.00  --sat_out_model                         small
% 4.04/1.00  --sat_out_clauses                       false
% 4.04/1.00  
% 4.04/1.00  ------ QBF Options
% 4.04/1.00  
% 4.04/1.00  --qbf_mode                              false
% 4.04/1.00  --qbf_elim_univ                         false
% 4.04/1.00  --qbf_dom_inst                          none
% 4.04/1.00  --qbf_dom_pre_inst                      false
% 4.04/1.00  --qbf_sk_in                             false
% 4.04/1.00  --qbf_pred_elim                         true
% 4.04/1.00  --qbf_split                             512
% 4.04/1.00  
% 4.04/1.00  ------ BMC1 Options
% 4.04/1.00  
% 4.04/1.00  --bmc1_incremental                      false
% 4.04/1.00  --bmc1_axioms                           reachable_all
% 4.04/1.00  --bmc1_min_bound                        0
% 4.04/1.00  --bmc1_max_bound                        -1
% 4.04/1.00  --bmc1_max_bound_default                -1
% 4.04/1.00  --bmc1_symbol_reachability              true
% 4.04/1.00  --bmc1_property_lemmas                  false
% 4.04/1.00  --bmc1_k_induction                      false
% 4.04/1.00  --bmc1_non_equiv_states                 false
% 4.04/1.00  --bmc1_deadlock                         false
% 4.04/1.00  --bmc1_ucm                              false
% 4.04/1.00  --bmc1_add_unsat_core                   none
% 4.04/1.00  --bmc1_unsat_core_children              false
% 4.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.00  --bmc1_out_stat                         full
% 4.04/1.00  --bmc1_ground_init                      false
% 4.04/1.00  --bmc1_pre_inst_next_state              false
% 4.04/1.00  --bmc1_pre_inst_state                   false
% 4.04/1.00  --bmc1_pre_inst_reach_state             false
% 4.04/1.00  --bmc1_out_unsat_core                   false
% 4.04/1.00  --bmc1_aig_witness_out                  false
% 4.04/1.00  --bmc1_verbose                          false
% 4.04/1.00  --bmc1_dump_clauses_tptp                false
% 4.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.00  --bmc1_dump_file                        -
% 4.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.00  --bmc1_ucm_extend_mode                  1
% 4.04/1.00  --bmc1_ucm_init_mode                    2
% 4.04/1.00  --bmc1_ucm_cone_mode                    none
% 4.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.00  --bmc1_ucm_relax_model                  4
% 4.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.00  --bmc1_ucm_layered_model                none
% 4.04/1.00  --bmc1_ucm_max_lemma_size               10
% 4.04/1.00  
% 4.04/1.00  ------ AIG Options
% 4.04/1.00  
% 4.04/1.00  --aig_mode                              false
% 4.04/1.00  
% 4.04/1.00  ------ Instantiation Options
% 4.04/1.00  
% 4.04/1.00  --instantiation_flag                    true
% 4.04/1.00  --inst_sos_flag                         false
% 4.04/1.00  --inst_sos_phase                        true
% 4.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel_side                     num_symb
% 4.04/1.00  --inst_solver_per_active                1400
% 4.04/1.00  --inst_solver_calls_frac                1.
% 4.04/1.00  --inst_passive_queue_type               priority_queues
% 4.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.00  --inst_passive_queues_freq              [25;2]
% 4.04/1.00  --inst_dismatching                      true
% 4.04/1.00  --inst_eager_unprocessed_to_passive     true
% 4.04/1.00  --inst_prop_sim_given                   true
% 4.04/1.00  --inst_prop_sim_new                     false
% 4.04/1.00  --inst_subs_new                         false
% 4.04/1.00  --inst_eq_res_simp                      false
% 4.04/1.00  --inst_subs_given                       false
% 4.04/1.00  --inst_orphan_elimination               true
% 4.04/1.00  --inst_learning_loop_flag               true
% 4.04/1.00  --inst_learning_start                   3000
% 4.04/1.00  --inst_learning_factor                  2
% 4.04/1.00  --inst_start_prop_sim_after_learn       3
% 4.04/1.00  --inst_sel_renew                        solver
% 4.04/1.00  --inst_lit_activity_flag                true
% 4.04/1.00  --inst_restr_to_given                   false
% 4.04/1.00  --inst_activity_threshold               500
% 4.04/1.00  --inst_out_proof                        true
% 4.04/1.00  
% 4.04/1.00  ------ Resolution Options
% 4.04/1.00  
% 4.04/1.00  --resolution_flag                       true
% 4.04/1.00  --res_lit_sel                           adaptive
% 4.04/1.00  --res_lit_sel_side                      none
% 4.04/1.00  --res_ordering                          kbo
% 4.04/1.00  --res_to_prop_solver                    active
% 4.04/1.00  --res_prop_simpl_new                    false
% 4.04/1.00  --res_prop_simpl_given                  true
% 4.04/1.00  --res_passive_queue_type                priority_queues
% 4.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.00  --res_passive_queues_freq               [15;5]
% 4.04/1.00  --res_forward_subs                      full
% 4.04/1.00  --res_backward_subs                     full
% 4.04/1.00  --res_forward_subs_resolution           true
% 4.04/1.00  --res_backward_subs_resolution          true
% 4.04/1.00  --res_orphan_elimination                true
% 4.04/1.00  --res_time_limit                        2.
% 4.04/1.00  --res_out_proof                         true
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Options
% 4.04/1.00  
% 4.04/1.00  --superposition_flag                    true
% 4.04/1.00  --sup_passive_queue_type                priority_queues
% 4.04/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.00  --sup_passive_queues_freq               [1;4]
% 4.04/1.00  --demod_completeness_check              fast
% 4.04/1.00  --demod_use_ground                      true
% 4.04/1.00  --sup_to_prop_solver                    passive
% 4.04/1.00  --sup_prop_simpl_new                    true
% 4.04/1.00  --sup_prop_simpl_given                  true
% 4.04/1.00  --sup_fun_splitting                     false
% 4.04/1.00  --sup_smt_interval                      50000
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Simplification Setup
% 4.04/1.00  
% 4.04/1.00  --sup_indices_passive                   []
% 4.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_full_bw                           [BwDemod]
% 4.04/1.00  --sup_immed_triv                        [TrivRules]
% 4.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_immed_bw_main                     []
% 4.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  
% 4.04/1.00  ------ Combination Options
% 4.04/1.00  
% 4.04/1.00  --comb_res_mult                         3
% 4.04/1.00  --comb_sup_mult                         2
% 4.04/1.00  --comb_inst_mult                        10
% 4.04/1.00  
% 4.04/1.00  ------ Debug Options
% 4.04/1.00  
% 4.04/1.00  --dbg_backtrace                         false
% 4.04/1.00  --dbg_dump_prop_clauses                 false
% 4.04/1.00  --dbg_dump_prop_clauses_file            -
% 4.04/1.00  --dbg_out_stat                          false
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  ------ Proving...
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  % SZS status Theorem for theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  fof(f2,axiom,(
% 4.04/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f14,plain,(
% 4.04/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.04/1.00    inference(rectify,[],[f2])).
% 4.04/1.00  
% 4.04/1.00  fof(f17,plain,(
% 4.04/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.04/1.00    inference(ennf_transformation,[],[f14])).
% 4.04/1.00  
% 4.04/1.00  fof(f33,plain,(
% 4.04/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f34,plain,(
% 4.04/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f33])).
% 4.04/1.00  
% 4.04/1.00  fof(f51,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f34])).
% 4.04/1.00  
% 4.04/1.00  fof(f12,conjecture,(
% 4.04/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f13,negated_conjecture,(
% 4.04/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.04/1.00    inference(negated_conjecture,[],[f12])).
% 4.04/1.00  
% 4.04/1.00  fof(f15,plain,(
% 4.04/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.04/1.00    inference(pure_predicate_removal,[],[f13])).
% 4.04/1.00  
% 4.04/1.00  fof(f16,plain,(
% 4.04/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.04/1.00    inference(pure_predicate_removal,[],[f15])).
% 4.04/1.00  
% 4.04/1.00  fof(f26,plain,(
% 4.04/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f16])).
% 4.04/1.00  
% 4.04/1.00  fof(f27,plain,(
% 4.04/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 4.04/1.00    inference(flattening,[],[f26])).
% 4.04/1.00  
% 4.04/1.00  fof(f42,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) => ((r1_tsep_1(sK5,X2) | r1_tsep_1(X2,sK5)) & (~r1_tsep_1(sK5,X1) | ~r1_tsep_1(X1,sK5)) & m1_pre_topc(X1,X2) & m1_pre_topc(sK5,X0))) )),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f41,plain,(
% 4.04/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) => (? [X3] : ((r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,sK4) & m1_pre_topc(X3,X0)) & m1_pre_topc(sK4,X0))) )),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f40,plain,(
% 4.04/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK3,X0))) )),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f39,plain,(
% 4.04/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) & m1_pre_topc(X1,sK2)) & l1_pre_topc(sK2))),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f43,plain,(
% 4.04/1.00    ((((r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & (~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2)) & m1_pre_topc(sK4,sK2)) & m1_pre_topc(sK3,sK2)) & l1_pre_topc(sK2)),
% 4.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f42,f41,f40,f39])).
% 4.04/1.00  
% 4.04/1.00  fof(f70,plain,(
% 4.04/1.00    m1_pre_topc(sK3,sK4)),
% 4.04/1.00    inference(cnf_transformation,[],[f43])).
% 4.04/1.00  
% 4.04/1.00  fof(f11,axiom,(
% 4.04/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f25,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f11])).
% 4.04/1.00  
% 4.04/1.00  fof(f65,plain,(
% 4.04/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f25])).
% 4.04/1.00  
% 4.04/1.00  fof(f6,axiom,(
% 4.04/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f37,plain,(
% 4.04/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.04/1.00    inference(nnf_transformation,[],[f6])).
% 4.04/1.00  
% 4.04/1.00  fof(f58,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f37])).
% 4.04/1.00  
% 4.04/1.00  fof(f5,axiom,(
% 4.04/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f18,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 4.04/1.00    inference(ennf_transformation,[],[f5])).
% 4.04/1.00  
% 4.04/1.00  fof(f19,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 4.04/1.00    inference(flattening,[],[f18])).
% 4.04/1.00  
% 4.04/1.00  fof(f57,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f19])).
% 4.04/1.00  
% 4.04/1.00  fof(f4,axiom,(
% 4.04/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f56,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f4])).
% 4.04/1.00  
% 4.04/1.00  fof(f3,axiom,(
% 4.04/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f35,plain,(
% 4.04/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.00    inference(nnf_transformation,[],[f3])).
% 4.04/1.00  
% 4.04/1.00  fof(f36,plain,(
% 4.04/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.00    inference(flattening,[],[f35])).
% 4.04/1.00  
% 4.04/1.00  fof(f55,plain,(
% 4.04/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f36])).
% 4.04/1.00  
% 4.04/1.00  fof(f53,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.04/1.00    inference(cnf_transformation,[],[f36])).
% 4.04/1.00  
% 4.04/1.00  fof(f77,plain,(
% 4.04/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.04/1.00    inference(equality_resolution,[],[f53])).
% 4.04/1.00  
% 4.04/1.00  fof(f66,plain,(
% 4.04/1.00    l1_pre_topc(sK2)),
% 4.04/1.00    inference(cnf_transformation,[],[f43])).
% 4.04/1.00  
% 4.04/1.00  fof(f8,axiom,(
% 4.04/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f21,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f8])).
% 4.04/1.00  
% 4.04/1.00  fof(f61,plain,(
% 4.04/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f21])).
% 4.04/1.00  
% 4.04/1.00  fof(f68,plain,(
% 4.04/1.00    m1_pre_topc(sK4,sK2)),
% 4.04/1.00    inference(cnf_transformation,[],[f43])).
% 4.04/1.00  
% 4.04/1.00  fof(f1,axiom,(
% 4.04/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f28,plain,(
% 4.04/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.04/1.00    inference(nnf_transformation,[],[f1])).
% 4.04/1.00  
% 4.04/1.00  fof(f29,plain,(
% 4.04/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.04/1.00    inference(flattening,[],[f28])).
% 4.04/1.00  
% 4.04/1.00  fof(f30,plain,(
% 4.04/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.04/1.00    inference(rectify,[],[f29])).
% 4.04/1.00  
% 4.04/1.00  fof(f31,plain,(
% 4.04/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f32,plain,(
% 4.04/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 4.04/1.00  
% 4.04/1.00  fof(f46,plain,(
% 4.04/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 4.04/1.00    inference(cnf_transformation,[],[f32])).
% 4.04/1.00  
% 4.04/1.00  fof(f73,plain,(
% 4.04/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 4.04/1.00    inference(equality_resolution,[],[f46])).
% 4.04/1.00  
% 4.04/1.00  fof(f50,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f34])).
% 4.04/1.00  
% 4.04/1.00  fof(f9,axiom,(
% 4.04/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f22,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f9])).
% 4.04/1.00  
% 4.04/1.00  fof(f38,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 4.04/1.00    inference(nnf_transformation,[],[f22])).
% 4.04/1.00  
% 4.04/1.00  fof(f62,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f38])).
% 4.04/1.00  
% 4.04/1.00  fof(f52,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f34])).
% 4.04/1.00  
% 4.04/1.00  fof(f10,axiom,(
% 4.04/1.00    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f23,plain,(
% 4.04/1.00    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 4.04/1.00    inference(ennf_transformation,[],[f10])).
% 4.04/1.00  
% 4.04/1.00  fof(f24,plain,(
% 4.04/1.00    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 4.04/1.00    inference(flattening,[],[f23])).
% 4.04/1.00  
% 4.04/1.00  fof(f64,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f24])).
% 4.04/1.00  
% 4.04/1.00  fof(f72,plain,(
% 4.04/1.00    r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)),
% 4.04/1.00    inference(cnf_transformation,[],[f43])).
% 4.04/1.00  
% 4.04/1.00  fof(f69,plain,(
% 4.04/1.00    m1_pre_topc(sK5,sK2)),
% 4.04/1.00    inference(cnf_transformation,[],[f43])).
% 4.04/1.00  
% 4.04/1.00  fof(f7,axiom,(
% 4.04/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f20,plain,(
% 4.04/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f7])).
% 4.04/1.00  
% 4.04/1.00  fof(f60,plain,(
% 4.04/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f20])).
% 4.04/1.00  
% 4.04/1.00  fof(f63,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f38])).
% 4.04/1.00  
% 4.04/1.00  fof(f71,plain,(
% 4.04/1.00    ~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)),
% 4.04/1.00    inference(cnf_transformation,[],[f43])).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7,plain,
% 4.04/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f51]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1152,plain,
% 4.04/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 4.04/1.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_24,negated_conjecture,
% 4.04/1.00      ( m1_pre_topc(sK3,sK4) ),
% 4.04/1.00      inference(cnf_transformation,[],[f70]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1136,plain,
% 4.04/1.00      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_21,plain,
% 4.04/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.04/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.04/1.00      | ~ l1_pre_topc(X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f65]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1139,plain,
% 4.04/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 4.04/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.04/1.00      | l1_pre_topc(X1) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_15,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f58]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1145,plain,
% 4.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.04/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1732,plain,
% 4.04/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 4.04/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 4.04/1.00      | l1_pre_topc(X1) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1139,c_1145]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_13,plain,
% 4.04/1.00      ( ~ r1_tarski(X0,X1)
% 4.04/1.00      | ~ r1_tarski(X2,X1)
% 4.04/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1147,plain,
% 4.04/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.04/1.00      | r1_tarski(X2,X1) != iProver_top
% 4.04/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_12,plain,
% 4.04/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 4.04/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1148,plain,
% 4.04/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_9,plain,
% 4.04/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.04/1.00      inference(cnf_transformation,[],[f55]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1150,plain,
% 4.04/1.00      ( X0 = X1
% 4.04/1.00      | r1_tarski(X0,X1) != iProver_top
% 4.04/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2229,plain,
% 4.04/1.00      ( k2_xboole_0(X0,X1) = X0
% 4.04/1.00      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1148,c_1150]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3539,plain,
% 4.04/1.00      ( k2_xboole_0(X0,X1) = X0
% 4.04/1.00      | r1_tarski(X0,X0) != iProver_top
% 4.04/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1147,c_2229]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_11,plain,
% 4.04/1.00      ( r1_tarski(X0,X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f77]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_62,plain,
% 4.04/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3986,plain,
% 4.04/1.00      ( k2_xboole_0(X0,X1) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_3539,c_62]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3995,plain,
% 4.04/1.00      ( k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
% 4.04/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 4.04/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1732,c_3986]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8419,plain,
% 4.04/1.00      ( k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) = u1_struct_0(sK4)
% 4.04/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1136,c_3995]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_28,negated_conjecture,
% 4.04/1.00      ( l1_pre_topc(sK2) ),
% 4.04/1.00      inference(cnf_transformation,[],[f66]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_29,plain,
% 4.04/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_17,plain,
% 4.04/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f61]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_26,negated_conjecture,
% 4.04/1.00      ( m1_pre_topc(sK4,sK2) ),
% 4.04/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1465,plain,
% 4.04/1.00      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 4.04/1.00      inference(resolution,[status(thm)],[c_17,c_26]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1466,plain,
% 4.04/1.00      ( l1_pre_topc(sK2) != iProver_top
% 4.04/1.00      | l1_pre_topc(sK4) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_1465]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8520,plain,
% 4.04/1.00      ( k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK3)) = u1_struct_0(sK4) ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_8419,c_29,c_1466]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3,plain,
% 4.04/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 4.04/1.00      inference(cnf_transformation,[],[f73]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1156,plain,
% 4.04/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.04/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8539,plain,
% 4.04/1.00      ( r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 4.04/1.00      | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_8520,c_1156]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_9228,plain,
% 4.04/1.00      ( r1_xboole_0(X0,u1_struct_0(sK3)) = iProver_top
% 4.04/1.00      | r2_hidden(sK1(X0,u1_struct_0(sK3)),u1_struct_0(sK4)) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1152,c_8539]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8,plain,
% 4.04/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f50]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1151,plain,
% 4.04/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 4.04/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_19,plain,
% 4.04/1.00      ( ~ r1_tsep_1(X0,X1)
% 4.04/1.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 4.04/1.00      | ~ l1_struct_0(X1)
% 4.04/1.00      | ~ l1_struct_0(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f62]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1141,plain,
% 4.04/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 4.04/1.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 4.04/1.00      | l1_struct_0(X1) != iProver_top
% 4.04/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_6,plain,
% 4.04/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f52]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1153,plain,
% 4.04/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 4.04/1.00      | r2_hidden(X2,X1) != iProver_top
% 4.04/1.00      | r2_hidden(X2,X0) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2292,plain,
% 4.04/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 4.04/1.00      | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
% 4.04/1.00      | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
% 4.04/1.00      | l1_struct_0(X1) != iProver_top
% 4.04/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1141,c_1153]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3690,plain,
% 4.04/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 4.04/1.00      | r1_xboole_0(u1_struct_0(X1),X2) = iProver_top
% 4.04/1.00      | r2_hidden(sK1(u1_struct_0(X1),X2),u1_struct_0(X0)) != iProver_top
% 4.04/1.00      | l1_struct_0(X1) != iProver_top
% 4.04/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1151,c_2292]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_10329,plain,
% 4.04/1.00      ( r1_tsep_1(sK4,X0) != iProver_top
% 4.04/1.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 4.04/1.00      | l1_struct_0(X0) != iProver_top
% 4.04/1.00      | l1_struct_0(sK4) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_9228,c_3690]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_10364,plain,
% 4.04/1.00      ( r1_tsep_1(sK4,sK5) != iProver_top
% 4.04/1.00      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 4.04/1.00      | l1_struct_0(sK4) != iProver_top
% 4.04/1.00      | l1_struct_0(sK5) != iProver_top ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_10329]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_20,plain,
% 4.04/1.00      ( ~ r1_tsep_1(X0,X1)
% 4.04/1.00      | r1_tsep_1(X1,X0)
% 4.04/1.00      | ~ l1_struct_0(X1)
% 4.04/1.00      | ~ l1_struct_0(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f64]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2067,plain,
% 4.04/1.00      ( r1_tsep_1(sK3,sK5)
% 4.04/1.00      | ~ r1_tsep_1(sK5,sK3)
% 4.04/1.00      | ~ l1_struct_0(sK3)
% 4.04/1.00      | ~ l1_struct_0(sK5) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2068,plain,
% 4.04/1.00      ( r1_tsep_1(sK3,sK5) = iProver_top
% 4.04/1.00      | r1_tsep_1(sK5,sK3) != iProver_top
% 4.04/1.00      | l1_struct_0(sK3) != iProver_top
% 4.04/1.00      | l1_struct_0(sK5) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_2067]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_22,negated_conjecture,
% 4.04/1.00      ( r1_tsep_1(sK4,sK5) | r1_tsep_1(sK5,sK4) ),
% 4.04/1.00      inference(cnf_transformation,[],[f72]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1937,plain,
% 4.04/1.00      ( r1_tsep_1(sK5,sK4) | ~ l1_struct_0(sK4) | ~ l1_struct_0(sK5) ),
% 4.04/1.00      inference(resolution,[status(thm)],[c_20,c_22]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_25,negated_conjecture,
% 4.04/1.00      ( m1_pre_topc(sK5,sK2) ),
% 4.04/1.00      inference(cnf_transformation,[],[f69]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_16,plain,
% 4.04/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f60]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_48,plain,
% 4.04/1.00      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1368,plain,
% 4.04/1.00      ( ~ m1_pre_topc(X0,sK2) | l1_pre_topc(X0) | ~ l1_pre_topc(sK2) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1370,plain,
% 4.04/1.00      ( ~ m1_pre_topc(sK5,sK2) | ~ l1_pre_topc(sK2) | l1_pre_topc(sK5) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_1368]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1524,plain,
% 4.04/1.00      ( l1_pre_topc(sK4) ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_1465,c_28]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1752,plain,
% 4.04/1.00      ( l1_struct_0(sK4) ),
% 4.04/1.00      inference(resolution,[status(thm)],[c_1524,c_16]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1138,plain,
% 4.04/1.00      ( r1_tsep_1(sK4,sK5) = iProver_top
% 4.04/1.00      | r1_tsep_1(sK5,sK4) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1140,plain,
% 4.04/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 4.04/1.00      | r1_tsep_1(X1,X0) = iProver_top
% 4.04/1.00      | l1_struct_0(X1) != iProver_top
% 4.04/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1916,plain,
% 4.04/1.00      ( r1_tsep_1(sK5,sK4) = iProver_top
% 4.04/1.00      | l1_struct_0(sK4) != iProver_top
% 4.04/1.00      | l1_struct_0(sK5) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1138,c_1140]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1917,plain,
% 4.04/1.00      ( r1_tsep_1(sK5,sK4) | ~ l1_struct_0(sK4) | ~ l1_struct_0(sK5) ),
% 4.04/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1916]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1940,plain,
% 4.04/1.00      ( r1_tsep_1(sK5,sK4) ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_1937,c_28,c_25,c_48,c_1370,c_1752,c_1917]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2048,plain,
% 4.04/1.00      ( r1_tsep_1(sK4,sK5) | ~ l1_struct_0(sK4) | ~ l1_struct_0(sK5) ),
% 4.04/1.00      inference(resolution,[status(thm)],[c_1940,c_20]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2049,plain,
% 4.04/1.00      ( r1_tsep_1(sK4,sK5) = iProver_top
% 4.04/1.00      | l1_struct_0(sK4) != iProver_top
% 4.04/1.00      | l1_struct_0(sK5) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_2048]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_18,plain,
% 4.04/1.00      ( r1_tsep_1(X0,X1)
% 4.04/1.00      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 4.04/1.00      | ~ l1_struct_0(X1)
% 4.04/1.00      | ~ l1_struct_0(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f63]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1948,plain,
% 4.04/1.00      ( r1_tsep_1(sK5,sK3)
% 4.04/1.00      | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
% 4.04/1.00      | ~ l1_struct_0(sK3)
% 4.04/1.00      | ~ l1_struct_0(sK5) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1949,plain,
% 4.04/1.00      ( r1_tsep_1(sK5,sK3) = iProver_top
% 4.04/1.00      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 4.04/1.00      | l1_struct_0(sK3) != iProver_top
% 4.04/1.00      | l1_struct_0(sK5) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_1948]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1753,plain,
% 4.04/1.00      ( l1_struct_0(sK4) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_1752]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1461,plain,
% 4.04/1.00      ( l1_pre_topc(sK3) | ~ l1_pre_topc(sK4) ),
% 4.04/1.00      inference(resolution,[status(thm)],[c_17,c_24]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1470,plain,
% 4.04/1.00      ( l1_pre_topc(sK3) ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_1461,c_28,c_1465]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1482,plain,
% 4.04/1.00      ( l1_struct_0(sK3) ),
% 4.04/1.00      inference(resolution,[status(thm)],[c_1470,c_16]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1483,plain,
% 4.04/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_1482]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1369,plain,
% 4.04/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 4.04/1.00      | l1_pre_topc(X0) = iProver_top
% 4.04/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_1368]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1371,plain,
% 4.04/1.00      ( m1_pre_topc(sK5,sK2) != iProver_top
% 4.04/1.00      | l1_pre_topc(sK2) != iProver_top
% 4.04/1.00      | l1_pre_topc(sK5) = iProver_top ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_1369]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_47,plain,
% 4.04/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_49,plain,
% 4.04/1.00      ( l1_pre_topc(sK5) != iProver_top
% 4.04/1.00      | l1_struct_0(sK5) = iProver_top ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_47]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_23,negated_conjecture,
% 4.04/1.00      ( ~ r1_tsep_1(sK3,sK5) | ~ r1_tsep_1(sK5,sK3) ),
% 4.04/1.00      inference(cnf_transformation,[],[f71]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_34,plain,
% 4.04/1.00      ( r1_tsep_1(sK3,sK5) != iProver_top
% 4.04/1.00      | r1_tsep_1(sK5,sK3) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_32,plain,
% 4.04/1.00      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(contradiction,plain,
% 4.04/1.00      ( $false ),
% 4.04/1.00      inference(minisat,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_10364,c_2068,c_2049,c_1949,c_1753,c_1483,c_1371,c_49,
% 4.04/1.00                 c_34,c_32,c_29]) ).
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  ------                               Statistics
% 4.04/1.00  
% 4.04/1.00  ------ Selected
% 4.04/1.00  
% 4.04/1.00  total_time:                             0.409
% 4.04/1.00  
%------------------------------------------------------------------------------

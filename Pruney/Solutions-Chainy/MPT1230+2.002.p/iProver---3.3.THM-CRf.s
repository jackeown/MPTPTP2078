%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:36 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 374 expanded)
%              Number of clauses        :   53 (  63 expanded)
%              Number of leaves         :    7 ( 105 expanded)
%              Depth                    :   23
%              Number of atoms          :  543 (4273 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f15])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK4)
        & r2_hidden(X2,sK4)
        & v3_pre_topc(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(X1,X3)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & ( ! [X4] :
                ( ~ r1_xboole_0(X1,X4)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ? [X3] :
              ( r1_xboole_0(X1,X3)
              & r2_hidden(sK3,X3)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK3,k2_pre_topc(X0,X1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(X1,X4)
              | ~ r2_hidden(sK3,X4)
              | ~ v3_pre_topc(X4,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK3,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(sK2,X3)
                  & r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK2)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(sK2,X4)
                  | ~ r2_hidden(X2,X4)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,k2_pre_topc(X0,sK2)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,sK1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
                | ~ r2_hidden(X2,k2_pre_topc(sK1,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,sK1)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                | r2_hidden(X2,k2_pre_topc(sK1,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ( ( r1_xboole_0(sK2,sK4)
        & r2_hidden(sK3,sK4)
        & v3_pre_topc(sK4,sK1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(sK2,X4)
          | ~ r2_hidden(sK3,X4)
          | ~ v3_pre_topc(X4,sK1)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f20,f19,f18,f17])).

fof(f36,plain,
    ( r1_xboole_0(sK2,sK4)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f5])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK0(X0,X1,X2))
        & r2_hidden(X2,sK0(X0,X1,X2))
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK0(X0,X1,X2))
                    & r2_hidden(X2,sK0(X0,X1,X2))
                    & v3_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,
    ( v3_pre_topc(sK4,sK1)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK0(X0,X1,X2),X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(sK2,X4)
      | ~ r2_hidden(sK3,X4)
      | ~ v3_pre_topc(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK0(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X2,sK0(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,
    ( r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK2,sK4)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_xboole_0(X2,X0)
    | ~ r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_152,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ r1_xboole_0(X1,X0)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK1,X1)) ),
    inference(resolution,[status(thm)],[c_4,c_13])).

cnf(c_299,plain,
    ( ~ v3_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_6,c_152])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,negated_conjecture,
    ( v3_pre_topc(sK4,sK1)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_299,c_12,c_9,c_8])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ r2_hidden(X0_42,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(X0_42,sK4)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_303])).

cnf(c_554,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_555,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_2,plain,
    ( v3_pre_topc(sK0(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_247,plain,
    ( v3_pre_topc(sK0(sK1,X0,X1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k2_pre_topc(sK1,X0))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_251,plain,
    ( r2_hidden(X1,k2_pre_topc(sK1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK0(sK1,X0,X1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_247,c_14])).

cnf(c_252,plain,
    ( v3_pre_topc(sK0(sK1,X0,X1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k2_pre_topc(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_251])).

cnf(c_10,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_xboole_0(sK2,X0)
    | ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_xboole_0(X0,sK0(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r1_xboole_0(X0,sK0(sK1,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK1,X0))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_0,c_13])).

cnf(c_228,plain,
    ( r2_hidden(X1,k2_pre_topc(sK1,X0))
    | r1_xboole_0(X0,sK0(sK1,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_224,c_14])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r1_xboole_0(X0,sK0(sK1,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_322,plain,
    ( ~ v3_pre_topc(sK0(sK1,sK2,X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_10,c_229])).

cnf(c_326,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v3_pre_topc(sK0(sK1,sK2,X0),sK1)
    | r2_hidden(X0,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_12])).

cnf(c_327,plain,
    ( ~ v3_pre_topc(sK0(sK1,sK2,X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_252,c_327])).

cnf(c_399,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_12])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_399])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK2,X0_42),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0_42,k2_pre_topc(sK1,sK2))
    | ~ r2_hidden(sK3,sK0(sK1,sK2,X0_42))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_400])).

cnf(c_546,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK3,sK0(sK1,sK2,sK3))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_547,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK3,sK0(sK1,sK2,sK3)) != iProver_top
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK0(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,sK0(sK1,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK1,X0))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_1,c_13])).

cnf(c_205,plain,
    ( r2_hidden(X1,k2_pre_topc(sK1,X0))
    | r2_hidden(X1,sK0(sK1,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_201,c_14])).

cnf(c_206,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,sK0(sK1,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | r2_hidden(X1_42,sK0(sK1,X0_42,X1_42))
    | r2_hidden(X1_42,k2_pre_topc(sK1,X0_42)) ),
    inference(subtyping,[status(esa)],[c_206])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,sK0(sK1,X0_42,sK3))
    | r2_hidden(sK3,k2_pre_topc(sK1,X0_42)) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_542,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK3,sK0(sK1,X0_42,sK3)) = iProver_top
    | r2_hidden(sK3,k2_pre_topc(sK1,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_544,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,sK0(sK1,sK2,sK3)) = iProver_top
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_178,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k2_pre_topc(sK1,X0))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_3,c_13])).

cnf(c_182,plain,
    ( r2_hidden(X1,k2_pre_topc(sK1,X0))
    | m1_subset_1(sK0(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_178,c_14])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k2_pre_topc(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,X0_42,X1_42),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1_42,k2_pre_topc(sK1,X0_42)) ),
    inference(subtyping,[status(esa)],[c_183])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0_42,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,k2_pre_topc(sK1,X0_42)) ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_537,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,X0_42,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK3,k2_pre_topc(sK1,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_539,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_24,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK1,sK2)) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_18,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_555,c_547,c_544,c_539,c_24,c_18,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:01:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.77/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.77/0.97  
% 0.77/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.77/0.97  
% 0.77/0.97  ------  iProver source info
% 0.77/0.97  
% 0.77/0.97  git: date: 2020-06-30 10:37:57 +0100
% 0.77/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.77/0.97  git: non_committed_changes: false
% 0.77/0.97  git: last_make_outside_of_git: false
% 0.77/0.97  
% 0.77/0.97  ------ 
% 0.77/0.97  
% 0.77/0.97  ------ Input Options
% 0.77/0.97  
% 0.77/0.97  --out_options                           all
% 0.77/0.97  --tptp_safe_out                         true
% 0.77/0.97  --problem_path                          ""
% 0.77/0.97  --include_path                          ""
% 0.77/0.97  --clausifier                            res/vclausify_rel
% 0.77/0.97  --clausifier_options                    --mode clausify
% 0.77/0.97  --stdin                                 false
% 0.77/0.97  --stats_out                             all
% 0.77/0.97  
% 0.77/0.97  ------ General Options
% 0.77/0.97  
% 0.77/0.97  --fof                                   false
% 0.77/0.97  --time_out_real                         305.
% 0.77/0.97  --time_out_virtual                      -1.
% 0.77/0.97  --symbol_type_check                     false
% 0.77/0.97  --clausify_out                          false
% 0.77/0.97  --sig_cnt_out                           false
% 0.77/0.97  --trig_cnt_out                          false
% 0.77/0.97  --trig_cnt_out_tolerance                1.
% 0.77/0.97  --trig_cnt_out_sk_spl                   false
% 0.77/0.97  --abstr_cl_out                          false
% 0.77/0.97  
% 0.77/0.97  ------ Global Options
% 0.77/0.97  
% 0.77/0.97  --schedule                              default
% 0.77/0.97  --add_important_lit                     false
% 0.77/0.97  --prop_solver_per_cl                    1000
% 0.77/0.97  --min_unsat_core                        false
% 0.77/0.97  --soft_assumptions                      false
% 0.77/0.97  --soft_lemma_size                       3
% 0.77/0.97  --prop_impl_unit_size                   0
% 0.77/0.97  --prop_impl_unit                        []
% 0.77/0.97  --share_sel_clauses                     true
% 0.77/0.97  --reset_solvers                         false
% 0.77/0.97  --bc_imp_inh                            [conj_cone]
% 0.77/0.97  --conj_cone_tolerance                   3.
% 0.77/0.97  --extra_neg_conj                        none
% 0.77/0.97  --large_theory_mode                     true
% 0.77/0.97  --prolific_symb_bound                   200
% 0.77/0.97  --lt_threshold                          2000
% 0.77/0.97  --clause_weak_htbl                      true
% 0.77/0.97  --gc_record_bc_elim                     false
% 0.77/0.97  
% 0.77/0.97  ------ Preprocessing Options
% 0.77/0.97  
% 0.77/0.97  --preprocessing_flag                    true
% 0.77/0.97  --time_out_prep_mult                    0.1
% 0.77/0.97  --splitting_mode                        input
% 0.77/0.97  --splitting_grd                         true
% 0.77/0.97  --splitting_cvd                         false
% 0.77/0.97  --splitting_cvd_svl                     false
% 0.77/0.97  --splitting_nvd                         32
% 0.77/0.97  --sub_typing                            true
% 0.77/0.97  --prep_gs_sim                           true
% 0.77/0.97  --prep_unflatten                        true
% 0.77/0.97  --prep_res_sim                          true
% 0.77/0.97  --prep_upred                            true
% 0.77/0.97  --prep_sem_filter                       exhaustive
% 0.77/0.97  --prep_sem_filter_out                   false
% 0.77/0.97  --pred_elim                             true
% 0.77/0.97  --res_sim_input                         true
% 0.77/0.97  --eq_ax_congr_red                       true
% 0.77/0.97  --pure_diseq_elim                       true
% 0.77/0.97  --brand_transform                       false
% 0.77/0.97  --non_eq_to_eq                          false
% 0.77/0.97  --prep_def_merge                        true
% 0.77/0.97  --prep_def_merge_prop_impl              false
% 0.77/0.97  --prep_def_merge_mbd                    true
% 0.77/0.97  --prep_def_merge_tr_red                 false
% 0.77/0.97  --prep_def_merge_tr_cl                  false
% 0.77/0.97  --smt_preprocessing                     true
% 0.77/0.97  --smt_ac_axioms                         fast
% 0.77/0.97  --preprocessed_out                      false
% 0.77/0.97  --preprocessed_stats                    false
% 0.77/0.97  
% 0.77/0.97  ------ Abstraction refinement Options
% 0.77/0.97  
% 0.77/0.97  --abstr_ref                             []
% 0.77/0.97  --abstr_ref_prep                        false
% 0.77/0.97  --abstr_ref_until_sat                   false
% 0.77/0.97  --abstr_ref_sig_restrict                funpre
% 0.77/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.77/0.97  --abstr_ref_under                       []
% 0.77/0.97  
% 0.77/0.97  ------ SAT Options
% 0.77/0.97  
% 0.77/0.97  --sat_mode                              false
% 0.77/0.97  --sat_fm_restart_options                ""
% 0.77/0.97  --sat_gr_def                            false
% 0.77/0.97  --sat_epr_types                         true
% 0.77/0.97  --sat_non_cyclic_types                  false
% 0.77/0.97  --sat_finite_models                     false
% 0.77/0.97  --sat_fm_lemmas                         false
% 0.77/0.97  --sat_fm_prep                           false
% 0.77/0.97  --sat_fm_uc_incr                        true
% 0.77/0.97  --sat_out_model                         small
% 0.77/0.97  --sat_out_clauses                       false
% 0.77/0.97  
% 0.77/0.97  ------ QBF Options
% 0.77/0.97  
% 0.77/0.97  --qbf_mode                              false
% 0.77/0.97  --qbf_elim_univ                         false
% 0.77/0.97  --qbf_dom_inst                          none
% 0.77/0.97  --qbf_dom_pre_inst                      false
% 0.77/0.97  --qbf_sk_in                             false
% 0.77/0.97  --qbf_pred_elim                         true
% 0.77/0.97  --qbf_split                             512
% 0.77/0.97  
% 0.77/0.97  ------ BMC1 Options
% 0.77/0.97  
% 0.77/0.97  --bmc1_incremental                      false
% 0.77/0.97  --bmc1_axioms                           reachable_all
% 0.77/0.97  --bmc1_min_bound                        0
% 0.77/0.97  --bmc1_max_bound                        -1
% 0.77/0.97  --bmc1_max_bound_default                -1
% 0.77/0.97  --bmc1_symbol_reachability              true
% 0.77/0.97  --bmc1_property_lemmas                  false
% 0.77/0.97  --bmc1_k_induction                      false
% 0.77/0.97  --bmc1_non_equiv_states                 false
% 0.77/0.97  --bmc1_deadlock                         false
% 0.77/0.97  --bmc1_ucm                              false
% 0.77/0.97  --bmc1_add_unsat_core                   none
% 0.77/0.97  --bmc1_unsat_core_children              false
% 0.77/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.77/0.97  --bmc1_out_stat                         full
% 0.77/0.97  --bmc1_ground_init                      false
% 0.77/0.97  --bmc1_pre_inst_next_state              false
% 0.77/0.97  --bmc1_pre_inst_state                   false
% 0.77/0.97  --bmc1_pre_inst_reach_state             false
% 0.77/0.97  --bmc1_out_unsat_core                   false
% 0.77/0.97  --bmc1_aig_witness_out                  false
% 0.77/0.97  --bmc1_verbose                          false
% 0.77/0.97  --bmc1_dump_clauses_tptp                false
% 0.77/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.77/0.97  --bmc1_dump_file                        -
% 0.77/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.77/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.77/0.97  --bmc1_ucm_extend_mode                  1
% 0.77/0.97  --bmc1_ucm_init_mode                    2
% 0.77/0.97  --bmc1_ucm_cone_mode                    none
% 0.77/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.77/0.97  --bmc1_ucm_relax_model                  4
% 0.77/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.77/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.77/0.97  --bmc1_ucm_layered_model                none
% 0.77/0.97  --bmc1_ucm_max_lemma_size               10
% 0.77/0.97  
% 0.77/0.97  ------ AIG Options
% 0.77/0.97  
% 0.77/0.97  --aig_mode                              false
% 0.77/0.97  
% 0.77/0.97  ------ Instantiation Options
% 0.77/0.97  
% 0.77/0.97  --instantiation_flag                    true
% 0.77/0.97  --inst_sos_flag                         false
% 0.77/0.97  --inst_sos_phase                        true
% 0.77/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.77/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.77/0.97  --inst_lit_sel_side                     num_symb
% 0.77/0.97  --inst_solver_per_active                1400
% 0.77/0.97  --inst_solver_calls_frac                1.
% 0.77/0.97  --inst_passive_queue_type               priority_queues
% 0.77/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.77/0.97  --inst_passive_queues_freq              [25;2]
% 0.77/0.97  --inst_dismatching                      true
% 0.77/0.97  --inst_eager_unprocessed_to_passive     true
% 0.77/0.97  --inst_prop_sim_given                   true
% 0.77/0.97  --inst_prop_sim_new                     false
% 0.77/0.97  --inst_subs_new                         false
% 0.77/0.97  --inst_eq_res_simp                      false
% 0.77/0.97  --inst_subs_given                       false
% 0.77/0.97  --inst_orphan_elimination               true
% 0.77/0.97  --inst_learning_loop_flag               true
% 0.77/0.97  --inst_learning_start                   3000
% 0.77/0.97  --inst_learning_factor                  2
% 0.77/0.97  --inst_start_prop_sim_after_learn       3
% 0.77/0.97  --inst_sel_renew                        solver
% 0.77/0.97  --inst_lit_activity_flag                true
% 0.77/0.97  --inst_restr_to_given                   false
% 0.77/0.97  --inst_activity_threshold               500
% 0.77/0.97  --inst_out_proof                        true
% 0.77/0.97  
% 0.77/0.97  ------ Resolution Options
% 0.77/0.97  
% 0.77/0.97  --resolution_flag                       true
% 0.77/0.97  --res_lit_sel                           adaptive
% 0.77/0.97  --res_lit_sel_side                      none
% 0.77/0.97  --res_ordering                          kbo
% 0.77/0.97  --res_to_prop_solver                    active
% 0.77/0.97  --res_prop_simpl_new                    false
% 0.77/0.97  --res_prop_simpl_given                  true
% 0.77/0.97  --res_passive_queue_type                priority_queues
% 0.77/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.77/0.97  --res_passive_queues_freq               [15;5]
% 0.77/0.97  --res_forward_subs                      full
% 0.77/0.97  --res_backward_subs                     full
% 0.77/0.97  --res_forward_subs_resolution           true
% 0.77/0.97  --res_backward_subs_resolution          true
% 0.77/0.97  --res_orphan_elimination                true
% 0.77/0.97  --res_time_limit                        2.
% 0.77/0.97  --res_out_proof                         true
% 0.77/0.97  
% 0.77/0.97  ------ Superposition Options
% 0.77/0.97  
% 0.77/0.97  --superposition_flag                    true
% 0.77/0.97  --sup_passive_queue_type                priority_queues
% 0.77/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.77/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.77/0.97  --demod_completeness_check              fast
% 0.77/0.97  --demod_use_ground                      true
% 0.77/0.97  --sup_to_prop_solver                    passive
% 0.77/0.97  --sup_prop_simpl_new                    true
% 0.77/0.97  --sup_prop_simpl_given                  true
% 0.77/0.97  --sup_fun_splitting                     false
% 0.77/0.97  --sup_smt_interval                      50000
% 0.77/0.97  
% 0.77/0.97  ------ Superposition Simplification Setup
% 0.77/0.97  
% 0.77/0.97  --sup_indices_passive                   []
% 0.77/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.77/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/0.97  --sup_full_bw                           [BwDemod]
% 0.77/0.97  --sup_immed_triv                        [TrivRules]
% 0.77/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.77/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/0.97  --sup_immed_bw_main                     []
% 0.77/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.77/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/0.97  
% 0.77/0.97  ------ Combination Options
% 0.77/0.97  
% 0.77/0.97  --comb_res_mult                         3
% 0.77/0.97  --comb_sup_mult                         2
% 0.77/0.97  --comb_inst_mult                        10
% 0.77/0.97  
% 0.77/0.97  ------ Debug Options
% 0.77/0.97  
% 0.77/0.97  --dbg_backtrace                         false
% 0.77/0.97  --dbg_dump_prop_clauses                 false
% 0.77/0.97  --dbg_dump_prop_clauses_file            -
% 0.77/0.97  --dbg_out_stat                          false
% 0.77/0.97  ------ Parsing...
% 0.77/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.77/0.97  
% 0.77/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.77/0.97  
% 0.77/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.77/0.97  ------ Proving...
% 0.77/0.97  ------ Problem Properties 
% 0.77/0.97  
% 0.77/0.97  
% 0.77/0.97  clauses                                 9
% 0.77/0.97  conjectures                             4
% 0.77/0.97  EPR                                     0
% 0.77/0.97  Horn                                    6
% 0.77/0.97  unary                                   2
% 0.77/0.97  binary                                  2
% 0.77/0.97  lits                                    29
% 0.77/0.97  lits eq                                 0
% 0.77/0.97  fd_pure                                 0
% 0.77/0.97  fd_pseudo                               0
% 0.77/0.97  fd_cond                                 0
% 0.77/0.97  fd_pseudo_cond                          0
% 0.77/0.97  AC symbols                              0
% 0.77/0.97  
% 0.77/0.97  ------ Schedule dynamic 5 is on 
% 0.77/0.97  
% 0.77/0.97  ------ no equalities: superposition off 
% 0.77/0.97  
% 0.77/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.77/0.97  
% 0.77/0.97  
% 0.77/0.97  ------ 
% 0.77/0.97  Current options:
% 0.77/0.97  ------ 
% 0.77/0.97  
% 0.77/0.97  ------ Input Options
% 0.77/0.97  
% 0.77/0.97  --out_options                           all
% 0.77/0.97  --tptp_safe_out                         true
% 0.77/0.97  --problem_path                          ""
% 0.77/0.97  --include_path                          ""
% 0.77/0.97  --clausifier                            res/vclausify_rel
% 0.77/0.97  --clausifier_options                    --mode clausify
% 0.77/0.97  --stdin                                 false
% 0.77/0.97  --stats_out                             all
% 0.77/0.97  
% 0.77/0.97  ------ General Options
% 0.77/0.97  
% 0.77/0.97  --fof                                   false
% 0.77/0.97  --time_out_real                         305.
% 0.77/0.97  --time_out_virtual                      -1.
% 0.77/0.97  --symbol_type_check                     false
% 0.77/0.97  --clausify_out                          false
% 0.77/0.97  --sig_cnt_out                           false
% 0.77/0.97  --trig_cnt_out                          false
% 0.77/0.97  --trig_cnt_out_tolerance                1.
% 0.77/0.97  --trig_cnt_out_sk_spl                   false
% 0.77/0.97  --abstr_cl_out                          false
% 0.77/0.97  
% 0.77/0.97  ------ Global Options
% 0.77/0.97  
% 0.77/0.97  --schedule                              default
% 0.77/0.97  --add_important_lit                     false
% 0.77/0.97  --prop_solver_per_cl                    1000
% 0.77/0.97  --min_unsat_core                        false
% 0.77/0.97  --soft_assumptions                      false
% 0.77/0.97  --soft_lemma_size                       3
% 0.77/0.97  --prop_impl_unit_size                   0
% 0.77/0.97  --prop_impl_unit                        []
% 0.77/0.97  --share_sel_clauses                     true
% 0.77/0.97  --reset_solvers                         false
% 0.77/0.97  --bc_imp_inh                            [conj_cone]
% 0.77/0.97  --conj_cone_tolerance                   3.
% 0.77/0.98  --extra_neg_conj                        none
% 0.77/0.98  --large_theory_mode                     true
% 0.77/0.98  --prolific_symb_bound                   200
% 0.77/0.98  --lt_threshold                          2000
% 0.77/0.98  --clause_weak_htbl                      true
% 0.77/0.98  --gc_record_bc_elim                     false
% 0.77/0.98  
% 0.77/0.98  ------ Preprocessing Options
% 0.77/0.98  
% 0.77/0.98  --preprocessing_flag                    true
% 0.77/0.98  --time_out_prep_mult                    0.1
% 0.77/0.98  --splitting_mode                        input
% 0.77/0.98  --splitting_grd                         true
% 0.77/0.98  --splitting_cvd                         false
% 0.77/0.98  --splitting_cvd_svl                     false
% 0.77/0.98  --splitting_nvd                         32
% 0.77/0.98  --sub_typing                            true
% 0.77/0.98  --prep_gs_sim                           true
% 0.77/0.98  --prep_unflatten                        true
% 0.77/0.98  --prep_res_sim                          true
% 0.77/0.98  --prep_upred                            true
% 0.77/0.98  --prep_sem_filter                       exhaustive
% 0.77/0.98  --prep_sem_filter_out                   false
% 0.77/0.98  --pred_elim                             true
% 0.77/0.98  --res_sim_input                         true
% 0.77/0.98  --eq_ax_congr_red                       true
% 0.77/0.98  --pure_diseq_elim                       true
% 0.77/0.98  --brand_transform                       false
% 0.77/0.98  --non_eq_to_eq                          false
% 0.77/0.98  --prep_def_merge                        true
% 0.77/0.98  --prep_def_merge_prop_impl              false
% 0.77/0.98  --prep_def_merge_mbd                    true
% 0.77/0.98  --prep_def_merge_tr_red                 false
% 0.77/0.98  --prep_def_merge_tr_cl                  false
% 0.77/0.98  --smt_preprocessing                     true
% 0.77/0.98  --smt_ac_axioms                         fast
% 0.77/0.98  --preprocessed_out                      false
% 0.77/0.98  --preprocessed_stats                    false
% 0.77/0.98  
% 0.77/0.98  ------ Abstraction refinement Options
% 0.77/0.98  
% 0.77/0.98  --abstr_ref                             []
% 0.77/0.98  --abstr_ref_prep                        false
% 0.77/0.98  --abstr_ref_until_sat                   false
% 0.77/0.98  --abstr_ref_sig_restrict                funpre
% 0.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.77/0.98  --abstr_ref_under                       []
% 0.77/0.98  
% 0.77/0.98  ------ SAT Options
% 0.77/0.98  
% 0.77/0.98  --sat_mode                              false
% 0.77/0.98  --sat_fm_restart_options                ""
% 0.77/0.98  --sat_gr_def                            false
% 0.77/0.98  --sat_epr_types                         true
% 0.77/0.98  --sat_non_cyclic_types                  false
% 0.77/0.98  --sat_finite_models                     false
% 0.77/0.98  --sat_fm_lemmas                         false
% 0.77/0.98  --sat_fm_prep                           false
% 0.77/0.98  --sat_fm_uc_incr                        true
% 0.77/0.98  --sat_out_model                         small
% 0.77/0.98  --sat_out_clauses                       false
% 0.77/0.98  
% 0.77/0.98  ------ QBF Options
% 0.77/0.98  
% 0.77/0.98  --qbf_mode                              false
% 0.77/0.98  --qbf_elim_univ                         false
% 0.77/0.98  --qbf_dom_inst                          none
% 0.77/0.98  --qbf_dom_pre_inst                      false
% 0.77/0.98  --qbf_sk_in                             false
% 0.77/0.98  --qbf_pred_elim                         true
% 0.77/0.98  --qbf_split                             512
% 0.77/0.98  
% 0.77/0.98  ------ BMC1 Options
% 0.77/0.98  
% 0.77/0.98  --bmc1_incremental                      false
% 0.77/0.98  --bmc1_axioms                           reachable_all
% 0.77/0.98  --bmc1_min_bound                        0
% 0.77/0.98  --bmc1_max_bound                        -1
% 0.77/0.98  --bmc1_max_bound_default                -1
% 0.77/0.98  --bmc1_symbol_reachability              true
% 0.77/0.98  --bmc1_property_lemmas                  false
% 0.77/0.98  --bmc1_k_induction                      false
% 0.77/0.98  --bmc1_non_equiv_states                 false
% 0.77/0.98  --bmc1_deadlock                         false
% 0.77/0.98  --bmc1_ucm                              false
% 0.77/0.98  --bmc1_add_unsat_core                   none
% 0.77/0.98  --bmc1_unsat_core_children              false
% 0.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.77/0.98  --bmc1_out_stat                         full
% 0.77/0.98  --bmc1_ground_init                      false
% 0.77/0.98  --bmc1_pre_inst_next_state              false
% 0.77/0.98  --bmc1_pre_inst_state                   false
% 0.77/0.98  --bmc1_pre_inst_reach_state             false
% 0.77/0.98  --bmc1_out_unsat_core                   false
% 0.77/0.98  --bmc1_aig_witness_out                  false
% 0.77/0.98  --bmc1_verbose                          false
% 0.77/0.98  --bmc1_dump_clauses_tptp                false
% 0.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.77/0.98  --bmc1_dump_file                        -
% 0.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.77/0.98  --bmc1_ucm_extend_mode                  1
% 0.77/0.98  --bmc1_ucm_init_mode                    2
% 0.77/0.98  --bmc1_ucm_cone_mode                    none
% 0.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.77/0.98  --bmc1_ucm_relax_model                  4
% 0.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.77/0.98  --bmc1_ucm_layered_model                none
% 0.77/0.98  --bmc1_ucm_max_lemma_size               10
% 0.77/0.98  
% 0.77/0.98  ------ AIG Options
% 0.77/0.98  
% 0.77/0.98  --aig_mode                              false
% 0.77/0.98  
% 0.77/0.98  ------ Instantiation Options
% 0.77/0.98  
% 0.77/0.98  --instantiation_flag                    true
% 0.77/0.98  --inst_sos_flag                         false
% 0.77/0.98  --inst_sos_phase                        true
% 0.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.77/0.98  --inst_lit_sel_side                     none
% 0.77/0.98  --inst_solver_per_active                1400
% 0.77/0.98  --inst_solver_calls_frac                1.
% 0.77/0.98  --inst_passive_queue_type               priority_queues
% 0.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.77/0.98  --inst_passive_queues_freq              [25;2]
% 0.77/0.98  --inst_dismatching                      true
% 0.77/0.98  --inst_eager_unprocessed_to_passive     true
% 0.77/0.98  --inst_prop_sim_given                   true
% 0.77/0.98  --inst_prop_sim_new                     false
% 0.77/0.98  --inst_subs_new                         false
% 0.77/0.98  --inst_eq_res_simp                      false
% 0.77/0.98  --inst_subs_given                       false
% 0.77/0.98  --inst_orphan_elimination               true
% 0.77/0.98  --inst_learning_loop_flag               true
% 0.77/0.98  --inst_learning_start                   3000
% 0.77/0.98  --inst_learning_factor                  2
% 0.77/0.98  --inst_start_prop_sim_after_learn       3
% 0.77/0.98  --inst_sel_renew                        solver
% 0.77/0.98  --inst_lit_activity_flag                true
% 0.77/0.98  --inst_restr_to_given                   false
% 0.77/0.98  --inst_activity_threshold               500
% 0.77/0.98  --inst_out_proof                        true
% 0.77/0.98  
% 0.77/0.98  ------ Resolution Options
% 0.77/0.98  
% 0.77/0.98  --resolution_flag                       false
% 0.77/0.98  --res_lit_sel                           adaptive
% 0.77/0.98  --res_lit_sel_side                      none
% 0.77/0.98  --res_ordering                          kbo
% 0.77/0.98  --res_to_prop_solver                    active
% 0.77/0.98  --res_prop_simpl_new                    false
% 0.77/0.98  --res_prop_simpl_given                  true
% 0.77/0.98  --res_passive_queue_type                priority_queues
% 0.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.77/0.98  --res_passive_queues_freq               [15;5]
% 0.77/0.98  --res_forward_subs                      full
% 0.77/0.98  --res_backward_subs                     full
% 0.77/0.98  --res_forward_subs_resolution           true
% 0.77/0.98  --res_backward_subs_resolution          true
% 0.77/0.98  --res_orphan_elimination                true
% 0.77/0.98  --res_time_limit                        2.
% 0.77/0.98  --res_out_proof                         true
% 0.77/0.98  
% 0.77/0.98  ------ Superposition Options
% 0.77/0.98  
% 0.77/0.98  --superposition_flag                    false
% 0.77/0.98  --sup_passive_queue_type                priority_queues
% 0.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.77/0.98  --demod_completeness_check              fast
% 0.77/0.98  --demod_use_ground                      true
% 0.77/0.98  --sup_to_prop_solver                    passive
% 0.77/0.98  --sup_prop_simpl_new                    true
% 0.77/0.98  --sup_prop_simpl_given                  true
% 0.77/0.98  --sup_fun_splitting                     false
% 0.77/0.98  --sup_smt_interval                      50000
% 0.77/0.98  
% 0.77/0.98  ------ Superposition Simplification Setup
% 0.77/0.98  
% 0.77/0.98  --sup_indices_passive                   []
% 0.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/0.98  --sup_full_bw                           [BwDemod]
% 0.77/0.98  --sup_immed_triv                        [TrivRules]
% 0.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/0.98  --sup_immed_bw_main                     []
% 0.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.77/0.98  
% 0.77/0.98  ------ Combination Options
% 0.77/0.98  
% 0.77/0.98  --comb_res_mult                         3
% 0.77/0.98  --comb_sup_mult                         2
% 0.77/0.98  --comb_inst_mult                        10
% 0.77/0.98  
% 0.77/0.98  ------ Debug Options
% 0.77/0.98  
% 0.77/0.98  --dbg_backtrace                         false
% 0.77/0.98  --dbg_dump_prop_clauses                 false
% 0.77/0.98  --dbg_dump_prop_clauses_file            -
% 0.77/0.98  --dbg_out_stat                          false
% 0.77/0.98  
% 0.77/0.98  
% 0.77/0.98  
% 0.77/0.98  
% 0.77/0.98  ------ Proving...
% 0.77/0.98  
% 0.77/0.98  
% 0.77/0.98  % SZS status Theorem for theBenchmark.p
% 0.77/0.98  
% 0.77/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.77/0.98  
% 0.77/0.98  fof(f2,conjecture,(
% 0.77/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0)))))))),
% 0.77/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.77/0.98  
% 0.77/0.98  fof(f3,negated_conjecture,(
% 0.77/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0)))))))),
% 0.77/0.98    inference(negated_conjecture,[],[f2])).
% 0.77/0.98  
% 0.77/0.98  fof(f4,plain,(
% 0.77/0.98    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0)))))))),
% 0.77/0.98    inference(pure_predicate_removal,[],[f3])).
% 0.77/0.98  
% 0.77/0.98  fof(f7,plain,(
% 0.77/0.98    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <~> ! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.77/0.98    inference(ennf_transformation,[],[f4])).
% 0.77/0.98  
% 0.77/0.98  fof(f8,plain,(
% 0.77/0.98    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <~> ! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.77/0.98    inference(flattening,[],[f7])).
% 0.77/0.98  
% 0.77/0.98  fof(f14,plain,(
% 0.77/0.98    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.77/0.98    inference(nnf_transformation,[],[f8])).
% 0.77/0.98  
% 0.77/0.98  fof(f15,plain,(
% 0.77/0.98    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.77/0.98    inference(flattening,[],[f14])).
% 0.77/0.98  
% 0.77/0.98  fof(f16,plain,(
% 0.77/0.98    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.77/0.98    inference(rectify,[],[f15])).
% 0.77/0.98  
% 0.77/0.98  fof(f20,plain,(
% 0.77/0.98    ( ! [X2,X0,X1] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK4) & r2_hidden(X2,sK4) & v3_pre_topc(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.77/0.98    introduced(choice_axiom,[])).
% 0.77/0.98  
% 0.77/0.98  fof(f19,plain,(
% 0.77/0.98    ( ! [X0,X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) => ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(sK3,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK3,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(sK3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3,k2_pre_topc(X0,X1))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 0.77/0.98    introduced(choice_axiom,[])).
% 0.77/0.98  
% 0.77/0.98  fof(f18,plain,(
% 0.77/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : ((? [X3] : (r1_xboole_0(sK2,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,sK2))) & (! [X4] : (~r1_xboole_0(sK2,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,sK2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.77/0.98    introduced(choice_axiom,[])).
% 0.77/0.98  
% 0.77/0.98  fof(f17,plain,(
% 0.77/0.98    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(X2,k2_pre_topc(sK1,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(X2,k2_pre_topc(sK1,X1))) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.77/0.98    introduced(choice_axiom,[])).
% 0.77/0.98  
% 0.77/0.98  fof(f21,plain,(
% 0.77/0.98    ((((r1_xboole_0(sK2,sK4) & r2_hidden(sK3,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) | ~r2_hidden(sK3,k2_pre_topc(sK1,sK2))) & (! [X4] : (~r1_xboole_0(sK2,X4) | ~r2_hidden(sK3,X4) | ~v3_pre_topc(X4,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) | r2_hidden(sK3,k2_pre_topc(sK1,sK2))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f20,f19,f18,f17])).
% 0.77/0.98  
% 0.77/0.98  fof(f36,plain,(
% 0.77/0.98    r1_xboole_0(sK2,sK4) | ~r2_hidden(sK3,k2_pre_topc(sK1,sK2))),
% 0.77/0.98    inference(cnf_transformation,[],[f21])).
% 0.77/0.98  
% 0.77/0.98  fof(f1,axiom,(
% 0.77/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 0.77/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.77/0.98  
% 0.77/0.98  fof(f5,plain,(
% 0.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.98    inference(ennf_transformation,[],[f1])).
% 0.77/0.98  
% 0.77/0.98  fof(f6,plain,(
% 0.77/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.98    inference(flattening,[],[f5])).
% 0.77/0.98  
% 0.77/0.98  fof(f9,plain,(
% 0.77/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.98    inference(nnf_transformation,[],[f6])).
% 0.77/0.98  
% 0.77/0.98  fof(f10,plain,(
% 0.77/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.98    inference(flattening,[],[f9])).
% 0.77/0.98  
% 0.77/0.98  fof(f11,plain,(
% 0.77/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.98    inference(rectify,[],[f10])).
% 0.77/0.98  
% 0.77/0.98  fof(f12,plain,(
% 0.77/0.98    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK0(X0,X1,X2)) & r2_hidden(X2,sK0(X0,X1,X2)) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.77/0.98    introduced(choice_axiom,[])).
% 0.77/0.98  
% 0.77/0.98  fof(f13,plain,(
% 0.77/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK0(X0,X1,X2)) & r2_hidden(X2,sK0(X0,X1,X2)) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 0.77/0.98  
% 0.77/0.98  fof(f23,plain,(
% 0.77/0.98    ( ! [X4,X2,X0,X1] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.77/0.98    inference(cnf_transformation,[],[f13])).
% 0.77/0.98  
% 0.77/0.98  fof(f29,plain,(
% 0.77/0.98    l1_pre_topc(sK1)),
% 0.77/0.98    inference(cnf_transformation,[],[f21])).
% 0.77/0.98  
% 0.77/0.98  fof(f30,plain,(
% 0.77/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.77/0.98    inference(cnf_transformation,[],[f21])).
% 0.77/0.98  
% 0.77/0.98  fof(f33,plain,(
% 0.77/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~r2_hidden(sK3,k2_pre_topc(sK1,sK2))),
% 0.77/0.98    inference(cnf_transformation,[],[f21])).
% 0.77/0.98  
% 0.77/0.98  fof(f34,plain,(
% 0.77/0.98    v3_pre_topc(sK4,sK1) | ~r2_hidden(sK3,k2_pre_topc(sK1,sK2))),
% 0.77/0.98    inference(cnf_transformation,[],[f21])).
% 0.77/0.98  
% 0.77/0.98  fof(f25,plain,(
% 0.77/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | v3_pre_topc(sK0(X0,X1,X2),X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.77/0.98    inference(cnf_transformation,[],[f13])).
% 0.77/0.98  
% 0.77/0.98  fof(f28,plain,(
% 0.77/0.98    ~v2_struct_0(sK1)),
% 0.77/0.98    inference(cnf_transformation,[],[f21])).
% 0.77/0.98  
% 0.77/0.98  fof(f32,plain,(
% 0.77/0.98    ( ! [X4] : (~r1_xboole_0(sK2,X4) | ~r2_hidden(sK3,X4) | ~v3_pre_topc(X4,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(sK3,k2_pre_topc(sK1,sK2))) )),
% 0.77/0.98    inference(cnf_transformation,[],[f21])).
% 0.77/0.98  
% 0.77/0.98  fof(f27,plain,(
% 0.77/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r1_xboole_0(X1,sK0(X0,X1,X2)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.77/0.98    inference(cnf_transformation,[],[f13])).
% 0.77/0.98  
% 0.77/0.98  fof(f26,plain,(
% 0.77/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r2_hidden(X2,sK0(X0,X1,X2)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.77/0.98    inference(cnf_transformation,[],[f13])).
% 0.77/0.98  
% 0.77/0.98  fof(f24,plain,(
% 0.77/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.77/0.98    inference(cnf_transformation,[],[f13])).
% 0.77/0.98  
% 0.77/0.98  fof(f35,plain,(
% 0.77/0.98    r2_hidden(sK3,sK4) | ~r2_hidden(sK3,k2_pre_topc(sK1,sK2))),
% 0.77/0.98    inference(cnf_transformation,[],[f21])).
% 0.77/0.98  
% 0.77/0.98  fof(f31,plain,(
% 0.77/0.98    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.77/0.98    inference(cnf_transformation,[],[f21])).
% 0.77/0.98  
% 0.77/0.98  cnf(c_6,negated_conjecture,
% 0.77/0.98      ( r1_xboole_0(sK2,sK4) | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(cnf_transformation,[],[f36]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_4,plain,
% 0.77/0.98      ( ~ v3_pre_topc(X0,X1)
% 0.77/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.77/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 0.77/0.98      | ~ r1_xboole_0(X2,X0)
% 0.77/0.98      | ~ r2_hidden(X3,X0)
% 0.77/0.98      | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
% 0.77/0.98      | ~ l1_pre_topc(X1) ),
% 0.77/0.98      inference(cnf_transformation,[],[f23]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_13,negated_conjecture,
% 0.77/0.98      ( l1_pre_topc(sK1) ),
% 0.77/0.98      inference(cnf_transformation,[],[f29]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_152,plain,
% 0.77/0.98      ( ~ v3_pre_topc(X0,sK1)
% 0.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 0.77/0.98      | ~ r1_xboole_0(X1,X0)
% 0.77/0.98      | ~ r2_hidden(X2,X0)
% 0.77/0.98      | ~ r2_hidden(X2,k2_pre_topc(sK1,X1)) ),
% 0.77/0.98      inference(resolution,[status(thm)],[c_4,c_13]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_299,plain,
% 0.77/0.98      ( ~ v3_pre_topc(sK4,sK1)
% 0.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ r2_hidden(X0,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(X0,sK4)
% 0.77/0.98      | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(resolution,[status(thm)],[c_6,c_152]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_12,negated_conjecture,
% 0.77/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.77/0.98      inference(cnf_transformation,[],[f30]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_9,negated_conjecture,
% 0.77/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(cnf_transformation,[],[f33]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_8,negated_conjecture,
% 0.77/0.98      ( v3_pre_topc(sK4,sK1) | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(cnf_transformation,[],[f34]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_303,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.77/0.98      | ~ r2_hidden(X0,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(X0,sK4)
% 0.77/0.98      | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(global_propositional_subsumption,
% 0.77/0.98                [status(thm)],
% 0.77/0.98                [c_299,c_12,c_9,c_8]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_485,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
% 0.77/0.98      | ~ r2_hidden(X0_42,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(X0_42,sK4)
% 0.77/0.98      | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(subtyping,[status(esa)],[c_303]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_554,plain,
% 0.77/0.98      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 0.77/0.98      | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(sK3,sK4) ),
% 0.77/0.98      inference(instantiation,[status(thm)],[c_485]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_555,plain,
% 0.77/0.98      ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) != iProver_top
% 0.77/0.98      | r2_hidden(sK3,sK4) != iProver_top ),
% 0.77/0.98      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_2,plain,
% 0.77/0.98      ( v3_pre_topc(sK0(X0,X1,X2),X0)
% 0.77/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.77/0.98      | r2_hidden(X2,k2_pre_topc(X0,X1))
% 0.77/0.98      | ~ l1_pre_topc(X0)
% 0.77/0.98      | v2_struct_0(X0) ),
% 0.77/0.98      inference(cnf_transformation,[],[f25]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_247,plain,
% 0.77/0.98      ( v3_pre_topc(sK0(sK1,X0,X1),sK1)
% 0.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | r2_hidden(X1,k2_pre_topc(sK1,X0))
% 0.77/0.98      | v2_struct_0(sK1) ),
% 0.77/0.98      inference(resolution,[status(thm)],[c_2,c_13]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_14,negated_conjecture,
% 0.77/0.98      ( ~ v2_struct_0(sK1) ),
% 0.77/0.98      inference(cnf_transformation,[],[f28]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_251,plain,
% 0.77/0.98      ( r2_hidden(X1,k2_pre_topc(sK1,X0))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | v3_pre_topc(sK0(sK1,X0,X1),sK1) ),
% 0.77/0.98      inference(global_propositional_subsumption,
% 0.77/0.98                [status(thm)],
% 0.77/0.98                [c_247,c_14]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_252,plain,
% 0.77/0.98      ( v3_pre_topc(sK0(sK1,X0,X1),sK1)
% 0.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | r2_hidden(X1,k2_pre_topc(sK1,X0)) ),
% 0.77/0.98      inference(renaming,[status(thm)],[c_251]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_10,negated_conjecture,
% 0.77/0.98      ( ~ v3_pre_topc(X0,sK1)
% 0.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ r1_xboole_0(sK2,X0)
% 0.77/0.98      | ~ r2_hidden(sK3,X0)
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(cnf_transformation,[],[f32]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_0,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.77/0.98      | r1_xboole_0(X0,sK0(X1,X0,X2))
% 0.77/0.98      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 0.77/0.98      | ~ l1_pre_topc(X1)
% 0.77/0.98      | v2_struct_0(X1) ),
% 0.77/0.98      inference(cnf_transformation,[],[f27]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_224,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | r1_xboole_0(X0,sK0(sK1,X0,X1))
% 0.77/0.98      | r2_hidden(X1,k2_pre_topc(sK1,X0))
% 0.77/0.98      | v2_struct_0(sK1) ),
% 0.77/0.98      inference(resolution,[status(thm)],[c_0,c_13]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_228,plain,
% 0.77/0.98      ( r2_hidden(X1,k2_pre_topc(sK1,X0))
% 0.77/0.98      | r1_xboole_0(X0,sK0(sK1,X0,X1))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.77/0.98      inference(global_propositional_subsumption,
% 0.77/0.98                [status(thm)],
% 0.77/0.98                [c_224,c_14]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_229,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | r1_xboole_0(X0,sK0(sK1,X0,X1))
% 0.77/0.98      | r2_hidden(X1,k2_pre_topc(sK1,X0)) ),
% 0.77/0.98      inference(renaming,[status(thm)],[c_228]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_322,plain,
% 0.77/0.98      ( ~ v3_pre_topc(sK0(sK1,sK2,X0),sK1)
% 0.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | r2_hidden(X0,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(resolution,[status(thm)],[c_10,c_229]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_326,plain,
% 0.77/0.98      ( ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.77/0.98      | ~ v3_pre_topc(sK0(sK1,sK2,X0),sK1)
% 0.77/0.98      | r2_hidden(X0,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(global_propositional_subsumption,
% 0.77/0.98                [status(thm)],
% 0.77/0.98                [c_322,c_12]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_327,plain,
% 0.77/0.98      ( ~ v3_pre_topc(sK0(sK1,sK2,X0),sK1)
% 0.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | r2_hidden(X0,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(renaming,[status(thm)],[c_326]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_395,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | r2_hidden(X0,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(resolution,[status(thm)],[c_252,c_327]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_399,plain,
% 0.77/0.98      ( ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.77/0.98      | r2_hidden(X0,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(global_propositional_subsumption,
% 0.77/0.98                [status(thm)],
% 0.77/0.98                [c_395,c_12]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_400,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(sK0(sK1,sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | r2_hidden(X0,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(sK3,sK0(sK1,sK2,X0))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(renaming,[status(thm)],[c_399]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_483,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0_42,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(sK0(sK1,sK2,X0_42),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | r2_hidden(X0_42,k2_pre_topc(sK1,sK2))
% 0.77/0.98      | ~ r2_hidden(sK3,sK0(sK1,sK2,X0_42))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(subtyping,[status(esa)],[c_400]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_546,plain,
% 0.77/0.98      ( ~ m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 0.77/0.98      | ~ r2_hidden(sK3,sK0(sK1,sK2,sK3))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
% 0.77/0.98      inference(instantiation,[status(thm)],[c_483]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_547,plain,
% 0.77/0.98      ( m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 0.77/0.98      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 0.77/0.98      | r2_hidden(sK3,sK0(sK1,sK2,sK3)) != iProver_top
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) = iProver_top ),
% 0.77/0.98      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_1,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.77/0.98      | r2_hidden(X2,sK0(X1,X0,X2))
% 0.77/0.98      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 0.77/0.98      | ~ l1_pre_topc(X1)
% 0.77/0.98      | v2_struct_0(X1) ),
% 0.77/0.98      inference(cnf_transformation,[],[f26]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_201,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | r2_hidden(X1,sK0(sK1,X0,X1))
% 0.77/0.98      | r2_hidden(X1,k2_pre_topc(sK1,X0))
% 0.77/0.98      | v2_struct_0(sK1) ),
% 0.77/0.98      inference(resolution,[status(thm)],[c_1,c_13]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_205,plain,
% 0.77/0.98      ( r2_hidden(X1,k2_pre_topc(sK1,X0))
% 0.77/0.98      | r2_hidden(X1,sK0(sK1,X0,X1))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.77/0.98      inference(global_propositional_subsumption,
% 0.77/0.98                [status(thm)],
% 0.77/0.98                [c_201,c_14]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_206,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | r2_hidden(X1,sK0(sK1,X0,X1))
% 0.77/0.98      | r2_hidden(X1,k2_pre_topc(sK1,X0)) ),
% 0.77/0.98      inference(renaming,[status(thm)],[c_205]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_486,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
% 0.77/0.98      | r2_hidden(X1_42,sK0(sK1,X0_42,X1_42))
% 0.77/0.98      | r2_hidden(X1_42,k2_pre_topc(sK1,X0_42)) ),
% 0.77/0.98      inference(subtyping,[status(esa)],[c_206]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_541,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 0.77/0.98      | r2_hidden(sK3,sK0(sK1,X0_42,sK3))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,X0_42)) ),
% 0.77/0.98      inference(instantiation,[status(thm)],[c_486]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_542,plain,
% 0.77/0.98      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 0.77/0.98      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 0.77/0.98      | r2_hidden(sK3,sK0(sK1,X0_42,sK3)) = iProver_top
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,X0_42)) = iProver_top ),
% 0.77/0.98      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_544,plain,
% 0.77/0.98      ( m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 0.77/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 0.77/0.98      | r2_hidden(sK3,sK0(sK1,sK2,sK3)) = iProver_top
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) = iProver_top ),
% 0.77/0.98      inference(instantiation,[status(thm)],[c_542]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_3,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.77/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 0.77/0.98      | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 0.77/0.98      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 0.77/0.98      | ~ l1_pre_topc(X1)
% 0.77/0.98      | v2_struct_0(X1) ),
% 0.77/0.98      inference(cnf_transformation,[],[f24]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_178,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | m1_subset_1(sK0(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | r2_hidden(X1,k2_pre_topc(sK1,X0))
% 0.77/0.98      | v2_struct_0(sK1) ),
% 0.77/0.98      inference(resolution,[status(thm)],[c_3,c_13]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_182,plain,
% 0.77/0.98      ( r2_hidden(X1,k2_pre_topc(sK1,X0))
% 0.77/0.98      | m1_subset_1(sK0(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.77/0.98      inference(global_propositional_subsumption,
% 0.77/0.98                [status(thm)],
% 0.77/0.98                [c_178,c_14]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_183,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.77/0.98      | m1_subset_1(sK0(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | r2_hidden(X1,k2_pre_topc(sK1,X0)) ),
% 0.77/0.98      inference(renaming,[status(thm)],[c_182]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_487,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(X1_42,u1_struct_0(sK1))
% 0.77/0.98      | m1_subset_1(sK0(sK1,X0_42,X1_42),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | r2_hidden(X1_42,k2_pre_topc(sK1,X0_42)) ),
% 0.77/0.98      inference(subtyping,[status(esa)],[c_183]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_536,plain,
% 0.77/0.98      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | m1_subset_1(sK0(sK1,X0_42,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.77/0.98      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,X0_42)) ),
% 0.77/0.98      inference(instantiation,[status(thm)],[c_487]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_537,plain,
% 0.77/0.98      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 0.77/0.98      | m1_subset_1(sK0(sK1,X0_42,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 0.77/0.98      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,X0_42)) = iProver_top ),
% 0.77/0.98      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_539,plain,
% 0.77/0.98      ( m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 0.77/0.98      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 0.77/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 0.77/0.98      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) = iProver_top ),
% 0.77/0.98      inference(instantiation,[status(thm)],[c_537]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_7,negated_conjecture,
% 0.77/0.98      ( ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) | r2_hidden(sK3,sK4) ),
% 0.77/0.98      inference(cnf_transformation,[],[f35]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_24,plain,
% 0.77/0.98      ( r2_hidden(sK3,k2_pre_topc(sK1,sK2)) != iProver_top
% 0.77/0.98      | r2_hidden(sK3,sK4) = iProver_top ),
% 0.77/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_11,negated_conjecture,
% 0.77/0.98      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 0.77/0.98      inference(cnf_transformation,[],[f31]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_18,plain,
% 0.77/0.98      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 0.77/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(c_17,plain,
% 0.77/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 0.77/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.77/0.98  
% 0.77/0.98  cnf(contradiction,plain,
% 0.77/0.98      ( $false ),
% 0.77/0.98      inference(minisat,
% 0.77/0.98                [status(thm)],
% 0.77/0.98                [c_555,c_547,c_544,c_539,c_24,c_18,c_17]) ).
% 0.77/0.98  
% 0.77/0.98  
% 0.77/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 0.77/0.98  
% 0.77/0.98  ------                               Statistics
% 0.77/0.98  
% 0.77/0.98  ------ General
% 0.77/0.98  
% 0.77/0.98  abstr_ref_over_cycles:                  0
% 0.77/0.98  abstr_ref_under_cycles:                 0
% 0.77/0.98  gc_basic_clause_elim:                   0
% 0.77/0.98  forced_gc_time:                         0
% 0.77/0.98  parsing_time:                           0.01
% 0.77/0.98  unif_index_cands_time:                  0.
% 0.77/0.98  unif_index_add_time:                    0.
% 0.77/0.98  orderings_time:                         0.
% 0.77/0.98  out_proof_time:                         0.011
% 0.77/0.98  total_time:                             0.054
% 0.77/0.98  num_of_symbols:                         45
% 0.77/0.98  num_of_terms:                           561
% 0.77/0.98  
% 0.77/0.98  ------ Preprocessing
% 0.77/0.98  
% 0.77/0.98  num_of_splits:                          0
% 0.77/0.98  num_of_split_atoms:                     0
% 0.77/0.98  num_of_reused_defs:                     0
% 0.77/0.98  num_eq_ax_congr_red:                    0
% 0.77/0.98  num_of_sem_filtered_clauses:            0
% 0.77/0.98  num_of_subtypes:                        3
% 0.77/0.98  monotx_restored_types:                  0
% 0.77/0.98  sat_num_of_epr_types:                   0
% 0.77/0.98  sat_num_of_non_cyclic_types:            0
% 0.77/0.98  sat_guarded_non_collapsed_types:        0
% 0.77/0.98  num_pure_diseq_elim:                    0
% 0.77/0.98  simp_replaced_by:                       0
% 0.77/0.98  res_preprocessed:                       24
% 0.77/0.98  prep_upred:                             0
% 0.77/0.98  prep_unflattend:                        0
% 0.77/0.98  smt_new_axioms:                         0
% 0.77/0.98  pred_elim_cands:                        2
% 0.77/0.98  pred_elim:                              4
% 0.77/0.98  pred_elim_cl:                           6
% 0.77/0.98  pred_elim_cycles:                       6
% 0.77/0.98  merged_defs:                            0
% 0.77/0.98  merged_defs_ncl:                        0
% 0.77/0.98  bin_hyper_res:                          0
% 0.77/0.98  prep_cycles:                            2
% 0.77/0.98  pred_elim_time:                         0.006
% 0.77/0.98  splitting_time:                         0.
% 0.77/0.98  sem_filter_time:                        0.
% 0.77/0.98  monotx_time:                            0.
% 0.77/0.98  subtype_inf_time:                       0.
% 0.77/0.98  
% 0.77/0.98  ------ Problem properties
% 0.77/0.98  
% 0.77/0.98  clauses:                                9
% 0.77/0.98  conjectures:                            4
% 0.77/0.98  epr:                                    0
% 0.77/0.98  horn:                                   6
% 0.77/0.98  ground:                                 4
% 0.77/0.98  unary:                                  2
% 0.77/0.98  binary:                                 2
% 0.77/0.98  lits:                                   29
% 0.77/0.98  lits_eq:                                0
% 0.77/0.98  fd_pure:                                0
% 0.77/0.98  fd_pseudo:                              0
% 0.77/0.98  fd_cond:                                0
% 0.77/0.98  fd_pseudo_cond:                         0
% 0.77/0.98  ac_symbols:                             0
% 0.77/0.98  
% 0.77/0.98  ------ Propositional Solver
% 0.77/0.98  
% 0.77/0.98  prop_solver_calls:                      14
% 0.77/0.98  prop_fast_solver_calls:                 258
% 0.77/0.98  smt_solver_calls:                       0
% 0.77/0.98  smt_fast_solver_calls:                  0
% 0.77/0.98  prop_num_of_clauses:                    140
% 0.77/0.98  prop_preprocess_simplified:             708
% 0.77/0.98  prop_fo_subsumed:                       11
% 0.77/0.98  prop_solver_time:                       0.
% 0.77/0.98  smt_solver_time:                        0.
% 0.77/0.98  smt_fast_solver_time:                   0.
% 0.77/0.98  prop_fast_solver_time:                  0.
% 0.77/0.98  prop_unsat_core_time:                   0.
% 0.77/0.98  
% 0.77/0.98  ------ QBF
% 0.77/0.98  
% 0.77/0.98  qbf_q_res:                              0
% 0.77/0.98  qbf_num_tautologies:                    0
% 0.77/0.98  qbf_prep_cycles:                        0
% 0.77/0.98  
% 0.77/0.98  ------ BMC1
% 0.77/0.98  
% 0.77/0.98  bmc1_current_bound:                     -1
% 0.77/0.98  bmc1_last_solved_bound:                 -1
% 0.77/0.98  bmc1_unsat_core_size:                   -1
% 0.77/0.98  bmc1_unsat_core_parents_size:           -1
% 0.77/0.98  bmc1_merge_next_fun:                    0
% 0.77/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.77/0.98  
% 0.77/0.98  ------ Instantiation
% 0.77/0.98  
% 0.77/0.98  inst_num_of_clauses:                    14
% 0.77/0.98  inst_num_in_passive:                    0
% 0.77/0.98  inst_num_in_active:                     13
% 0.77/0.98  inst_num_in_unprocessed:                0
% 0.77/0.98  inst_num_of_loops:                      19
% 0.77/0.98  inst_num_of_learning_restarts:          0
% 0.77/0.98  inst_num_moves_active_passive:          3
% 0.77/0.98  inst_lit_activity:                      0
% 0.77/0.98  inst_lit_activity_moves:                0
% 0.77/0.98  inst_num_tautologies:                   0
% 0.77/0.98  inst_num_prop_implied:                  0
% 0.77/0.98  inst_num_existing_simplified:           0
% 0.77/0.98  inst_num_eq_res_simplified:             0
% 0.77/0.98  inst_num_child_elim:                    0
% 0.77/0.98  inst_num_of_dismatching_blockings:      0
% 0.77/0.98  inst_num_of_non_proper_insts:           5
% 0.77/0.98  inst_num_of_duplicates:                 0
% 0.77/0.98  inst_inst_num_from_inst_to_res:         0
% 0.77/0.98  inst_dismatching_checking_time:         0.
% 0.77/0.98  
% 0.77/0.98  ------ Resolution
% 0.77/0.98  
% 0.77/0.98  res_num_of_clauses:                     0
% 0.77/0.98  res_num_in_passive:                     0
% 0.77/0.98  res_num_in_active:                      0
% 0.77/0.98  res_num_of_loops:                       26
% 0.77/0.98  res_forward_subset_subsumed:            1
% 0.77/0.98  res_backward_subset_subsumed:           0
% 0.77/0.98  res_forward_subsumed:                   0
% 0.77/0.98  res_backward_subsumed:                  0
% 0.77/0.98  res_forward_subsumption_resolution:     0
% 0.77/0.98  res_backward_subsumption_resolution:    0
% 0.77/0.98  res_clause_to_clause_subsumption:       7
% 0.77/0.98  res_orphan_elimination:                 0
% 0.77/0.98  res_tautology_del:                      1
% 0.77/0.98  res_num_eq_res_simplified:              0
% 0.77/0.98  res_num_sel_changes:                    0
% 0.77/0.98  res_moves_from_active_to_pass:          0
% 0.77/0.98  
% 0.77/0.98  ------ Superposition
% 0.77/0.98  
% 0.77/0.98  sup_time_total:                         0.
% 0.77/0.98  sup_time_generating:                    0.
% 0.77/0.98  sup_time_sim_full:                      0.
% 0.77/0.98  sup_time_sim_immed:                     0.
% 0.77/0.98  
% 0.77/0.98  sup_num_of_clauses:                     0
% 0.77/0.98  sup_num_in_active:                      0
% 0.77/0.98  sup_num_in_passive:                     0
% 0.77/0.98  sup_num_of_loops:                       0
% 0.77/0.98  sup_fw_superposition:                   0
% 0.77/0.98  sup_bw_superposition:                   0
% 0.77/0.98  sup_immediate_simplified:               0
% 0.77/0.98  sup_given_eliminated:                   0
% 0.77/0.98  comparisons_done:                       0
% 0.77/0.98  comparisons_avoided:                    0
% 0.77/0.98  
% 0.77/0.98  ------ Simplifications
% 0.77/0.98  
% 0.77/0.98  
% 0.77/0.98  sim_fw_subset_subsumed:                 0
% 0.77/0.98  sim_bw_subset_subsumed:                 0
% 0.77/0.98  sim_fw_subsumed:                        0
% 0.77/0.98  sim_bw_subsumed:                        0
% 0.77/0.98  sim_fw_subsumption_res:                 0
% 0.77/0.98  sim_bw_subsumption_res:                 0
% 0.77/0.98  sim_tautology_del:                      0
% 0.77/0.98  sim_eq_tautology_del:                   0
% 0.77/0.98  sim_eq_res_simp:                        0
% 0.77/0.98  sim_fw_demodulated:                     0
% 0.77/0.98  sim_bw_demodulated:                     0
% 0.77/0.98  sim_light_normalised:                   0
% 0.77/0.98  sim_joinable_taut:                      0
% 0.77/0.98  sim_joinable_simp:                      0
% 0.77/0.98  sim_ac_normalised:                      0
% 0.77/0.98  sim_smt_subsumption:                    0
% 0.77/0.98  
%------------------------------------------------------------------------------

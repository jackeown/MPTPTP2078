%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:47 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 620 expanded)
%              Number of clauses        :  110 ( 136 expanded)
%              Number of leaves         :   13 ( 171 expanded)
%              Depth                    :   18
%              Number of atoms          :  903 (5370 expanded)
%              Number of equality atoms :   90 (  90 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK1(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                    & r1_tarski(sK1(X0,X1,X2),X2)
                    & v3_pre_topc(sK1(X0,X1,X2),X0)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,conjecture,(
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
                    ( m1_connsp_2(X3,X0,X2)
                   => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
                      ( m1_connsp_2(X3,X0,X2)
                     => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f32])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r1_xboole_0(X3,X1)
          & m1_connsp_2(X3,X0,X2) )
     => ( r1_xboole_0(sK5,X1)
        & m1_connsp_2(sK5,X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(X3,X1)
                & m1_connsp_2(X3,X0,X2) )
            | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & ( ! [X4] :
                ( ~ r1_xboole_0(X4,X1)
                | ~ m1_connsp_2(X4,X0,X2) )
            | r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ? [X3] :
              ( r1_xboole_0(X3,X1)
              & m1_connsp_2(X3,X0,sK4) )
          | ~ r2_hidden(sK4,k2_pre_topc(X0,X1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(X4,X1)
              | ~ m1_connsp_2(X4,X0,sK4) )
          | r2_hidden(sK4,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,X0,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,X0,X2) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(X3,sK3)
                  & m1_connsp_2(X3,X0,X2) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK3)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X4,sK3)
                  | ~ m1_connsp_2(X4,X0,X2) )
              | r2_hidden(X2,k2_pre_topc(X0,sK3)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X3,X1)
                      & m1_connsp_2(X3,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X4,X1)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X3,X1)
                    & m1_connsp_2(X3,sK2,X2) )
                | ~ r2_hidden(X2,k2_pre_topc(sK2,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X4,X1)
                    | ~ m1_connsp_2(X4,sK2,X2) )
                | r2_hidden(X2,k2_pre_topc(sK2,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ( r1_xboole_0(sK5,sK3)
        & m1_connsp_2(sK5,sK2,sK4) )
      | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(X4,sK3)
          | ~ m1_connsp_2(X4,sK2,sK4) )
      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f37,f36,f35,f34])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(X4,sK3)
      | ~ m1_connsp_2(X4,sK2,sK4)
      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X2,sK0(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK0(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK0(X0,X1,X2),X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,
    ( r1_xboole_0(sK5,sK3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,
    ( m1_connsp_2(sK5,sK2,sK4)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_148,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_8])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_338,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_148,c_21])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_342,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK1(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_22,c_20])).

cnf(c_1124,plain,
    ( ~ m1_connsp_2(X0_46,sK2,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | r2_hidden(X1_46,sK1(sK2,X1_46,X0_46)) ),
    inference(subtyping,[status(esa)],[c_342])).

cnf(c_1245,plain,
    ( ~ m1_connsp_2(X0_46,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,sK1(sK2,sK4,X0_46)) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1500,plain,
    ( ~ m1_connsp_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,sK1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_1501,plain,
    ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,sK1(sK2,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r1_xboole_0(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_581,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK2,X1))
    | ~ r1_xboole_0(X1,X0) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

cnf(c_1117,plain,
    ( ~ v3_pre_topc(X0_46,sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | ~ r2_hidden(X2_46,X0_46)
    | ~ r2_hidden(X2_46,k2_pre_topc(sK2,X1_46))
    | ~ r1_xboole_0(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_581])).

cnf(c_1270,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK4,X0_46),sK2)
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,sK4,X0_46),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2_46,sK1(sK2,sK4,X0_46))
    | ~ r2_hidden(X2_46,k2_pre_topc(sK2,X1_46))
    | ~ r1_xboole_0(X1_46,sK1(sK2,sK4,X0_46)) ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_1362,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK4,X0_46),sK2)
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,sK4,X0_46),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK1(sK2,sK4,X0_46))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X1_46))
    | ~ r1_xboole_0(X1_46,sK1(sK2,sK4,X0_46)) ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_1428,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK4,sK5),sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK1(sK2,sK4,sK5))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_46))
    | ~ r1_xboole_0(X0_46,sK1(sK2,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_1432,plain,
    ( v3_pre_topc(sK1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,sK1(sK2,sK4,sK5)) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) != iProver_top
    | r1_xboole_0(X0_46,sK1(sK2,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_1434,plain,
    ( v3_pre_topc(sK1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,sK1(sK2,sK4,sK5)) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | r1_xboole_0(sK3,sK1(sK2,sK4,sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_127,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_8])).

cnf(c_398,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_127,c_21])).

cnf(c_402,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_22,c_20])).

cnf(c_1122,plain,
    ( ~ m1_connsp_2(X0_46,sK2,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1_46,X0_46),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_402])).

cnf(c_1225,plain,
    ( ~ m1_connsp_2(X0_46,sK2,sK4)
    | m1_subset_1(sK1(sK2,sK4,X0_46),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_1406,plain,
    ( ~ m1_connsp_2(sK5,sK2,sK4)
    | m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_1407,plain,
    ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_134,plain,
    ( v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_8])).

cnf(c_135,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_378,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | v3_pre_topc(sK1(sK2,X1,X0),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_135,c_21])).

cnf(c_382,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | v3_pre_topc(sK1(sK2,X1,X0),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_22,c_20])).

cnf(c_1123,plain,
    ( ~ m1_connsp_2(X0_46,sK2,X1_46)
    | v3_pre_topc(sK1(sK2,X1_46,X0_46),sK2)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_382])).

cnf(c_1230,plain,
    ( ~ m1_connsp_2(X0_46,sK2,sK4)
    | v3_pre_topc(sK1(sK2,sK4,X0_46),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_1391,plain,
    ( ~ m1_connsp_2(sK5,sK2,sK4)
    | v3_pre_topc(sK1(sK2,sK4,sK5),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_1392,plain,
    ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
    | v3_pre_topc(sK1(sK2,sK4,sK5),sK2) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1130,plain,
    ( ~ r1_xboole_0(X0_46,X1_46)
    | r1_xboole_0(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1303,plain,
    ( r1_xboole_0(X0_46,sK1(sK2,sK4,X1_46))
    | ~ r1_xboole_0(sK1(sK2,sK4,X1_46),X0_46) ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_1386,plain,
    ( r1_xboole_0(X0_46,sK1(sK2,sK4,sK5))
    | ~ r1_xboole_0(sK1(sK2,sK4,sK5),X0_46) ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_1387,plain,
    ( r1_xboole_0(X0_46,sK1(sK2,sK4,sK5)) = iProver_top
    | r1_xboole_0(sK1(sK2,sK4,sK5),X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1386])).

cnf(c_1389,plain,
    ( r1_xboole_0(sK1(sK2,sK4,sK5),sK3) != iProver_top
    | r1_xboole_0(sK3,sK1(sK2,sK4,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_9,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_450,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X0)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_9,c_21])).

cnf(c_454,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_22,c_20])).

cnf(c_1121,plain,
    ( m1_connsp_2(X0_46,sK2,X1_46)
    | ~ v3_pre_topc(X0_46,sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ r2_hidden(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_1281,plain,
    ( m1_connsp_2(sK0(sK2,X0_46,sK4),sK2,X1_46)
    | ~ v3_pre_topc(sK0(sK2,X0_46,sK4),sK2)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_46,sK0(sK2,X0_46,sK4)) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1357,plain,
    ( m1_connsp_2(sK0(sK2,X0_46,sK4),sK2,sK4)
    | ~ v3_pre_topc(sK0(sK2,X0_46,sK4),sK2)
    | ~ m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK0(sK2,X0_46,sK4)) ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_1358,plain,
    ( m1_connsp_2(sK0(sK2,X0_46,sK4),sK2,sK4) = iProver_top
    | v3_pre_topc(sK0(sK2,X0_46,sK4),sK2) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,sK0(sK2,X0_46,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1357])).

cnf(c_1360,plain,
    ( m1_connsp_2(sK0(sK2,sK3,sK4),sK2,sK4) = iProver_top
    | v3_pre_topc(sK0(sK2,sK3,sK4),sK2) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,sK0(sK2,sK3,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_17,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK2,sK4)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r1_xboole_0(X0,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1127,negated_conjecture,
    ( ~ m1_connsp_2(X0_46,sK2,sK4)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r1_xboole_0(X0_46,sK3) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1330,plain,
    ( ~ m1_connsp_2(sK0(sK2,sK3,sK4),sK2,sK4)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r1_xboole_0(sK0(sK2,sK3,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1333,plain,
    ( m1_connsp_2(sK0(sK2,sK3,sK4),sK2,sK4) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | r1_xboole_0(sK0(sK2,sK3,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_141,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_8])).

cnf(c_358,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_tarski(sK1(sK2,X1,X0),X0)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_141,c_21])).

cnf(c_362,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_tarski(sK1(sK2,X1,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_22,c_20])).

cnf(c_530,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(sK1(sK2,X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_1,c_362])).

cnf(c_1119,plain,
    ( ~ m1_connsp_2(X0_46,sK2,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ r1_xboole_0(X0_46,X2_46)
    | r1_xboole_0(sK1(sK2,X1_46,X0_46),X2_46) ),
    inference(subtyping,[status(esa)],[c_530])).

cnf(c_1260,plain,
    ( ~ m1_connsp_2(X0_46,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r1_xboole_0(X0_46,X1_46)
    | r1_xboole_0(sK1(sK2,sK4,X0_46),X1_46) ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_1323,plain,
    ( ~ m1_connsp_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r1_xboole_0(sK1(sK2,sK4,sK5),X0_46)
    | ~ r1_xboole_0(sK5,X0_46) ),
    inference(instantiation,[status(thm)],[c_1260])).

cnf(c_1324,plain,
    ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r1_xboole_0(sK1(sK2,sK4,sK5),X0_46) = iProver_top
    | r1_xboole_0(sK5,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_1326,plain,
    ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r1_xboole_0(sK1(sK2,sK4,sK5),sK3) = iProver_top
    | r1_xboole_0(sK5,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(c_1290,plain,
    ( ~ r1_xboole_0(X0_46,sK0(sK2,X0_46,sK4))
    | r1_xboole_0(sK0(sK2,X0_46,sK4),X0_46) ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_1291,plain,
    ( r1_xboole_0(X0_46,sK0(sK2,X0_46,sK4)) != iProver_top
    | r1_xboole_0(sK0(sK2,X0_46,sK4),X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1290])).

cnf(c_1293,plain,
    ( r1_xboole_0(sK0(sK2,sK3,sK4),sK3) = iProver_top
    | r1_xboole_0(sK3,sK0(sK2,sK3,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK0(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK0(sK2,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_3,c_20])).

cnf(c_634,plain,
    ( r2_hidden(X1,k2_pre_topc(sK2,X0))
    | r2_hidden(X1,sK0(sK2,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_22])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK0(sK2,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_1115,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | r2_hidden(X1_46,sK0(sK2,X0_46,X1_46))
    | r2_hidden(X1_46,k2_pre_topc(sK2,X0_46)) ),
    inference(subtyping,[status(esa)],[c_635])).

cnf(c_1255,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,sK0(sK2,X0_46,sK4))
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_1256,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,sK0(sK2,X0_46,sK4)) = iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1255])).

cnf(c_1258,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,sK0(sK2,sK3,sK4)) = iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | r1_xboole_0(X0,sK0(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | r1_xboole_0(X0,sK0(sK2,X0,X1))
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

cnf(c_657,plain,
    ( r1_xboole_0(X0,sK0(sK2,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_22])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | r1_xboole_0(X0,sK0(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_657])).

cnf(c_1114,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | r2_hidden(X1_46,k2_pre_topc(sK2,X0_46))
    | r1_xboole_0(X0_46,sK0(sK2,X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_658])).

cnf(c_1250,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_46))
    | r1_xboole_0(X0_46,sK0(sK2,X0_46,sK4)) ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_1251,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) = iProver_top
    | r1_xboole_0(X0_46,sK0(sK2,X0_46,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_1253,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | r1_xboole_0(sK3,sK0(sK2,sK3,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_607,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_5,c_20])).

cnf(c_611,plain,
    ( r2_hidden(X1,k2_pre_topc(sK2,X0))
    | m1_subset_1(sK0(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_22])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_611])).

cnf(c_1116,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_46,X1_46),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1_46,k2_pre_topc(sK2,X0_46)) ),
    inference(subtyping,[status(esa)],[c_612])).

cnf(c_1240,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_1241,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_1243,plain,
    ( m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1241])).

cnf(c_4,plain,
    ( v3_pre_topc(sK0(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_676,plain,
    ( v3_pre_topc(sK0(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_4,c_20])).

cnf(c_680,plain,
    ( r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK0(sK2,X0,X1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_22])).

cnf(c_681,plain,
    ( v3_pre_topc(sK0(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_680])).

cnf(c_1113,plain,
    ( v3_pre_topc(sK0(sK2,X0_46,X1_46),sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | r2_hidden(X1_46,k2_pre_topc(sK2,X0_46)) ),
    inference(subtyping,[status(esa)],[c_681])).

cnf(c_1235,plain,
    ( v3_pre_topc(sK0(sK2,X0_46,sK4),sK2)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_1236,plain,
    ( v3_pre_topc(sK0(sK2,X0_46,sK4),sK2) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_1238,plain,
    ( v3_pre_topc(sK0(sK2,sK3,sK4),sK2) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | r1_xboole_0(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(sK5,sK2,sK4)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,plain,
    ( m1_connsp_2(sK5,sK2,sK4) = iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1501,c_1434,c_1407,c_1392,c_1389,c_1360,c_1333,c_1326,c_1293,c_1258,c_1253,c_1243,c_1238,c_32,c_31,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:41:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.17/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.17/1.01  
% 1.17/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.17/1.01  
% 1.17/1.01  ------  iProver source info
% 1.17/1.01  
% 1.17/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.17/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.17/1.01  git: non_committed_changes: false
% 1.17/1.01  git: last_make_outside_of_git: false
% 1.17/1.01  
% 1.17/1.01  ------ 
% 1.17/1.01  
% 1.17/1.01  ------ Input Options
% 1.17/1.01  
% 1.17/1.01  --out_options                           all
% 1.17/1.01  --tptp_safe_out                         true
% 1.17/1.01  --problem_path                          ""
% 1.17/1.01  --include_path                          ""
% 1.17/1.01  --clausifier                            res/vclausify_rel
% 1.17/1.01  --clausifier_options                    --mode clausify
% 1.17/1.01  --stdin                                 false
% 1.17/1.01  --stats_out                             all
% 1.17/1.01  
% 1.17/1.01  ------ General Options
% 1.17/1.01  
% 1.17/1.01  --fof                                   false
% 1.17/1.01  --time_out_real                         305.
% 1.17/1.01  --time_out_virtual                      -1.
% 1.17/1.01  --symbol_type_check                     false
% 1.17/1.01  --clausify_out                          false
% 1.17/1.01  --sig_cnt_out                           false
% 1.17/1.01  --trig_cnt_out                          false
% 1.17/1.01  --trig_cnt_out_tolerance                1.
% 1.17/1.01  --trig_cnt_out_sk_spl                   false
% 1.17/1.01  --abstr_cl_out                          false
% 1.17/1.01  
% 1.17/1.01  ------ Global Options
% 1.17/1.01  
% 1.17/1.01  --schedule                              default
% 1.17/1.01  --add_important_lit                     false
% 1.17/1.01  --prop_solver_per_cl                    1000
% 1.17/1.01  --min_unsat_core                        false
% 1.17/1.01  --soft_assumptions                      false
% 1.17/1.01  --soft_lemma_size                       3
% 1.17/1.01  --prop_impl_unit_size                   0
% 1.17/1.01  --prop_impl_unit                        []
% 1.17/1.01  --share_sel_clauses                     true
% 1.17/1.01  --reset_solvers                         false
% 1.17/1.01  --bc_imp_inh                            [conj_cone]
% 1.17/1.01  --conj_cone_tolerance                   3.
% 1.17/1.01  --extra_neg_conj                        none
% 1.17/1.01  --large_theory_mode                     true
% 1.17/1.01  --prolific_symb_bound                   200
% 1.17/1.01  --lt_threshold                          2000
% 1.17/1.01  --clause_weak_htbl                      true
% 1.17/1.01  --gc_record_bc_elim                     false
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing Options
% 1.17/1.01  
% 1.17/1.01  --preprocessing_flag                    true
% 1.17/1.01  --time_out_prep_mult                    0.1
% 1.17/1.01  --splitting_mode                        input
% 1.17/1.01  --splitting_grd                         true
% 1.17/1.01  --splitting_cvd                         false
% 1.17/1.01  --splitting_cvd_svl                     false
% 1.17/1.01  --splitting_nvd                         32
% 1.17/1.01  --sub_typing                            true
% 1.17/1.01  --prep_gs_sim                           true
% 1.17/1.01  --prep_unflatten                        true
% 1.17/1.01  --prep_res_sim                          true
% 1.17/1.01  --prep_upred                            true
% 1.17/1.01  --prep_sem_filter                       exhaustive
% 1.17/1.01  --prep_sem_filter_out                   false
% 1.17/1.01  --pred_elim                             true
% 1.17/1.01  --res_sim_input                         true
% 1.17/1.01  --eq_ax_congr_red                       true
% 1.17/1.01  --pure_diseq_elim                       true
% 1.17/1.01  --brand_transform                       false
% 1.17/1.01  --non_eq_to_eq                          false
% 1.17/1.01  --prep_def_merge                        true
% 1.17/1.01  --prep_def_merge_prop_impl              false
% 1.17/1.01  --prep_def_merge_mbd                    true
% 1.17/1.01  --prep_def_merge_tr_red                 false
% 1.17/1.01  --prep_def_merge_tr_cl                  false
% 1.17/1.01  --smt_preprocessing                     true
% 1.17/1.01  --smt_ac_axioms                         fast
% 1.17/1.01  --preprocessed_out                      false
% 1.17/1.01  --preprocessed_stats                    false
% 1.17/1.01  
% 1.17/1.01  ------ Abstraction refinement Options
% 1.17/1.01  
% 1.17/1.01  --abstr_ref                             []
% 1.17/1.01  --abstr_ref_prep                        false
% 1.17/1.01  --abstr_ref_until_sat                   false
% 1.17/1.01  --abstr_ref_sig_restrict                funpre
% 1.17/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/1.01  --abstr_ref_under                       []
% 1.17/1.01  
% 1.17/1.01  ------ SAT Options
% 1.17/1.01  
% 1.17/1.01  --sat_mode                              false
% 1.17/1.01  --sat_fm_restart_options                ""
% 1.17/1.01  --sat_gr_def                            false
% 1.17/1.01  --sat_epr_types                         true
% 1.17/1.01  --sat_non_cyclic_types                  false
% 1.17/1.01  --sat_finite_models                     false
% 1.17/1.01  --sat_fm_lemmas                         false
% 1.17/1.01  --sat_fm_prep                           false
% 1.17/1.01  --sat_fm_uc_incr                        true
% 1.17/1.01  --sat_out_model                         small
% 1.17/1.01  --sat_out_clauses                       false
% 1.17/1.01  
% 1.17/1.01  ------ QBF Options
% 1.17/1.01  
% 1.17/1.01  --qbf_mode                              false
% 1.17/1.01  --qbf_elim_univ                         false
% 1.17/1.01  --qbf_dom_inst                          none
% 1.17/1.01  --qbf_dom_pre_inst                      false
% 1.17/1.01  --qbf_sk_in                             false
% 1.17/1.01  --qbf_pred_elim                         true
% 1.17/1.01  --qbf_split                             512
% 1.17/1.01  
% 1.17/1.01  ------ BMC1 Options
% 1.17/1.01  
% 1.17/1.01  --bmc1_incremental                      false
% 1.17/1.01  --bmc1_axioms                           reachable_all
% 1.17/1.01  --bmc1_min_bound                        0
% 1.17/1.01  --bmc1_max_bound                        -1
% 1.17/1.01  --bmc1_max_bound_default                -1
% 1.17/1.01  --bmc1_symbol_reachability              true
% 1.17/1.01  --bmc1_property_lemmas                  false
% 1.17/1.01  --bmc1_k_induction                      false
% 1.17/1.01  --bmc1_non_equiv_states                 false
% 1.17/1.01  --bmc1_deadlock                         false
% 1.17/1.01  --bmc1_ucm                              false
% 1.17/1.01  --bmc1_add_unsat_core                   none
% 1.17/1.01  --bmc1_unsat_core_children              false
% 1.17/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/1.01  --bmc1_out_stat                         full
% 1.17/1.01  --bmc1_ground_init                      false
% 1.17/1.01  --bmc1_pre_inst_next_state              false
% 1.17/1.01  --bmc1_pre_inst_state                   false
% 1.17/1.01  --bmc1_pre_inst_reach_state             false
% 1.17/1.01  --bmc1_out_unsat_core                   false
% 1.17/1.01  --bmc1_aig_witness_out                  false
% 1.17/1.01  --bmc1_verbose                          false
% 1.17/1.01  --bmc1_dump_clauses_tptp                false
% 1.17/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.17/1.01  --bmc1_dump_file                        -
% 1.17/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.17/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.17/1.01  --bmc1_ucm_extend_mode                  1
% 1.17/1.01  --bmc1_ucm_init_mode                    2
% 1.17/1.01  --bmc1_ucm_cone_mode                    none
% 1.17/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.17/1.01  --bmc1_ucm_relax_model                  4
% 1.17/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.17/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/1.01  --bmc1_ucm_layered_model                none
% 1.17/1.01  --bmc1_ucm_max_lemma_size               10
% 1.17/1.01  
% 1.17/1.01  ------ AIG Options
% 1.17/1.01  
% 1.17/1.01  --aig_mode                              false
% 1.17/1.01  
% 1.17/1.01  ------ Instantiation Options
% 1.17/1.01  
% 1.17/1.01  --instantiation_flag                    true
% 1.17/1.01  --inst_sos_flag                         false
% 1.17/1.01  --inst_sos_phase                        true
% 1.17/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/1.01  --inst_lit_sel_side                     num_symb
% 1.17/1.01  --inst_solver_per_active                1400
% 1.17/1.01  --inst_solver_calls_frac                1.
% 1.17/1.01  --inst_passive_queue_type               priority_queues
% 1.17/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/1.01  --inst_passive_queues_freq              [25;2]
% 1.17/1.01  --inst_dismatching                      true
% 1.17/1.01  --inst_eager_unprocessed_to_passive     true
% 1.17/1.01  --inst_prop_sim_given                   true
% 1.17/1.01  --inst_prop_sim_new                     false
% 1.17/1.01  --inst_subs_new                         false
% 1.17/1.01  --inst_eq_res_simp                      false
% 1.17/1.01  --inst_subs_given                       false
% 1.17/1.01  --inst_orphan_elimination               true
% 1.17/1.01  --inst_learning_loop_flag               true
% 1.17/1.01  --inst_learning_start                   3000
% 1.17/1.01  --inst_learning_factor                  2
% 1.17/1.01  --inst_start_prop_sim_after_learn       3
% 1.17/1.01  --inst_sel_renew                        solver
% 1.17/1.01  --inst_lit_activity_flag                true
% 1.17/1.01  --inst_restr_to_given                   false
% 1.17/1.01  --inst_activity_threshold               500
% 1.17/1.01  --inst_out_proof                        true
% 1.17/1.01  
% 1.17/1.01  ------ Resolution Options
% 1.17/1.01  
% 1.17/1.01  --resolution_flag                       true
% 1.17/1.01  --res_lit_sel                           adaptive
% 1.17/1.01  --res_lit_sel_side                      none
% 1.17/1.01  --res_ordering                          kbo
% 1.17/1.01  --res_to_prop_solver                    active
% 1.17/1.01  --res_prop_simpl_new                    false
% 1.17/1.01  --res_prop_simpl_given                  true
% 1.17/1.01  --res_passive_queue_type                priority_queues
% 1.17/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/1.01  --res_passive_queues_freq               [15;5]
% 1.17/1.01  --res_forward_subs                      full
% 1.17/1.01  --res_backward_subs                     full
% 1.17/1.01  --res_forward_subs_resolution           true
% 1.17/1.01  --res_backward_subs_resolution          true
% 1.17/1.01  --res_orphan_elimination                true
% 1.17/1.01  --res_time_limit                        2.
% 1.17/1.01  --res_out_proof                         true
% 1.17/1.01  
% 1.17/1.01  ------ Superposition Options
% 1.17/1.01  
% 1.17/1.01  --superposition_flag                    true
% 1.17/1.01  --sup_passive_queue_type                priority_queues
% 1.17/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.17/1.01  --demod_completeness_check              fast
% 1.17/1.01  --demod_use_ground                      true
% 1.17/1.01  --sup_to_prop_solver                    passive
% 1.17/1.01  --sup_prop_simpl_new                    true
% 1.17/1.01  --sup_prop_simpl_given                  true
% 1.17/1.01  --sup_fun_splitting                     false
% 1.17/1.01  --sup_smt_interval                      50000
% 1.17/1.01  
% 1.17/1.01  ------ Superposition Simplification Setup
% 1.17/1.01  
% 1.17/1.01  --sup_indices_passive                   []
% 1.17/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_full_bw                           [BwDemod]
% 1.17/1.01  --sup_immed_triv                        [TrivRules]
% 1.17/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_immed_bw_main                     []
% 1.17/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.01  
% 1.17/1.01  ------ Combination Options
% 1.17/1.01  
% 1.17/1.01  --comb_res_mult                         3
% 1.17/1.01  --comb_sup_mult                         2
% 1.17/1.01  --comb_inst_mult                        10
% 1.17/1.01  
% 1.17/1.01  ------ Debug Options
% 1.17/1.01  
% 1.17/1.01  --dbg_backtrace                         false
% 1.17/1.01  --dbg_dump_prop_clauses                 false
% 1.17/1.01  --dbg_dump_prop_clauses_file            -
% 1.17/1.01  --dbg_out_stat                          false
% 1.17/1.01  ------ Parsing...
% 1.17/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.17/1.01  ------ Proving...
% 1.17/1.01  ------ Problem Properties 
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  clauses                                 18
% 1.17/1.01  conjectures                             5
% 1.17/1.01  EPR                                     1
% 1.17/1.01  Horn                                    14
% 1.17/1.01  unary                                   2
% 1.17/1.01  binary                                  3
% 1.17/1.01  lits                                    60
% 1.17/1.01  lits eq                                 0
% 1.17/1.01  fd_pure                                 0
% 1.17/1.01  fd_pseudo                               0
% 1.17/1.01  fd_cond                                 0
% 1.17/1.01  fd_pseudo_cond                          0
% 1.17/1.01  AC symbols                              0
% 1.17/1.01  
% 1.17/1.01  ------ Schedule dynamic 5 is on 
% 1.17/1.01  
% 1.17/1.01  ------ no equalities: superposition off 
% 1.17/1.01  
% 1.17/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  ------ 
% 1.17/1.01  Current options:
% 1.17/1.01  ------ 
% 1.17/1.01  
% 1.17/1.01  ------ Input Options
% 1.17/1.01  
% 1.17/1.01  --out_options                           all
% 1.17/1.01  --tptp_safe_out                         true
% 1.17/1.01  --problem_path                          ""
% 1.17/1.01  --include_path                          ""
% 1.17/1.01  --clausifier                            res/vclausify_rel
% 1.17/1.01  --clausifier_options                    --mode clausify
% 1.17/1.01  --stdin                                 false
% 1.17/1.01  --stats_out                             all
% 1.17/1.01  
% 1.17/1.01  ------ General Options
% 1.17/1.01  
% 1.17/1.01  --fof                                   false
% 1.17/1.01  --time_out_real                         305.
% 1.17/1.01  --time_out_virtual                      -1.
% 1.17/1.01  --symbol_type_check                     false
% 1.17/1.01  --clausify_out                          false
% 1.17/1.01  --sig_cnt_out                           false
% 1.17/1.01  --trig_cnt_out                          false
% 1.17/1.01  --trig_cnt_out_tolerance                1.
% 1.17/1.01  --trig_cnt_out_sk_spl                   false
% 1.17/1.01  --abstr_cl_out                          false
% 1.17/1.01  
% 1.17/1.01  ------ Global Options
% 1.17/1.01  
% 1.17/1.01  --schedule                              default
% 1.17/1.01  --add_important_lit                     false
% 1.17/1.01  --prop_solver_per_cl                    1000
% 1.17/1.01  --min_unsat_core                        false
% 1.17/1.01  --soft_assumptions                      false
% 1.17/1.01  --soft_lemma_size                       3
% 1.17/1.01  --prop_impl_unit_size                   0
% 1.17/1.01  --prop_impl_unit                        []
% 1.17/1.01  --share_sel_clauses                     true
% 1.17/1.01  --reset_solvers                         false
% 1.17/1.01  --bc_imp_inh                            [conj_cone]
% 1.17/1.01  --conj_cone_tolerance                   3.
% 1.17/1.01  --extra_neg_conj                        none
% 1.17/1.01  --large_theory_mode                     true
% 1.17/1.01  --prolific_symb_bound                   200
% 1.17/1.01  --lt_threshold                          2000
% 1.17/1.01  --clause_weak_htbl                      true
% 1.17/1.01  --gc_record_bc_elim                     false
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing Options
% 1.17/1.01  
% 1.17/1.01  --preprocessing_flag                    true
% 1.17/1.01  --time_out_prep_mult                    0.1
% 1.17/1.01  --splitting_mode                        input
% 1.17/1.01  --splitting_grd                         true
% 1.17/1.01  --splitting_cvd                         false
% 1.17/1.01  --splitting_cvd_svl                     false
% 1.17/1.01  --splitting_nvd                         32
% 1.17/1.01  --sub_typing                            true
% 1.17/1.01  --prep_gs_sim                           true
% 1.17/1.01  --prep_unflatten                        true
% 1.17/1.01  --prep_res_sim                          true
% 1.17/1.01  --prep_upred                            true
% 1.17/1.01  --prep_sem_filter                       exhaustive
% 1.17/1.01  --prep_sem_filter_out                   false
% 1.17/1.01  --pred_elim                             true
% 1.17/1.01  --res_sim_input                         true
% 1.17/1.01  --eq_ax_congr_red                       true
% 1.17/1.01  --pure_diseq_elim                       true
% 1.17/1.01  --brand_transform                       false
% 1.17/1.01  --non_eq_to_eq                          false
% 1.17/1.01  --prep_def_merge                        true
% 1.17/1.01  --prep_def_merge_prop_impl              false
% 1.17/1.01  --prep_def_merge_mbd                    true
% 1.17/1.01  --prep_def_merge_tr_red                 false
% 1.17/1.01  --prep_def_merge_tr_cl                  false
% 1.17/1.01  --smt_preprocessing                     true
% 1.17/1.01  --smt_ac_axioms                         fast
% 1.17/1.01  --preprocessed_out                      false
% 1.17/1.01  --preprocessed_stats                    false
% 1.17/1.01  
% 1.17/1.01  ------ Abstraction refinement Options
% 1.17/1.01  
% 1.17/1.01  --abstr_ref                             []
% 1.17/1.01  --abstr_ref_prep                        false
% 1.17/1.01  --abstr_ref_until_sat                   false
% 1.17/1.01  --abstr_ref_sig_restrict                funpre
% 1.17/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/1.01  --abstr_ref_under                       []
% 1.17/1.01  
% 1.17/1.01  ------ SAT Options
% 1.17/1.01  
% 1.17/1.01  --sat_mode                              false
% 1.17/1.01  --sat_fm_restart_options                ""
% 1.17/1.01  --sat_gr_def                            false
% 1.17/1.01  --sat_epr_types                         true
% 1.17/1.01  --sat_non_cyclic_types                  false
% 1.17/1.01  --sat_finite_models                     false
% 1.17/1.01  --sat_fm_lemmas                         false
% 1.17/1.01  --sat_fm_prep                           false
% 1.17/1.01  --sat_fm_uc_incr                        true
% 1.17/1.01  --sat_out_model                         small
% 1.17/1.01  --sat_out_clauses                       false
% 1.17/1.01  
% 1.17/1.01  ------ QBF Options
% 1.17/1.01  
% 1.17/1.01  --qbf_mode                              false
% 1.17/1.01  --qbf_elim_univ                         false
% 1.17/1.01  --qbf_dom_inst                          none
% 1.17/1.01  --qbf_dom_pre_inst                      false
% 1.17/1.01  --qbf_sk_in                             false
% 1.17/1.01  --qbf_pred_elim                         true
% 1.17/1.01  --qbf_split                             512
% 1.17/1.01  
% 1.17/1.01  ------ BMC1 Options
% 1.17/1.01  
% 1.17/1.01  --bmc1_incremental                      false
% 1.17/1.01  --bmc1_axioms                           reachable_all
% 1.17/1.01  --bmc1_min_bound                        0
% 1.17/1.01  --bmc1_max_bound                        -1
% 1.17/1.01  --bmc1_max_bound_default                -1
% 1.17/1.01  --bmc1_symbol_reachability              true
% 1.17/1.01  --bmc1_property_lemmas                  false
% 1.17/1.01  --bmc1_k_induction                      false
% 1.17/1.01  --bmc1_non_equiv_states                 false
% 1.17/1.01  --bmc1_deadlock                         false
% 1.17/1.01  --bmc1_ucm                              false
% 1.17/1.01  --bmc1_add_unsat_core                   none
% 1.17/1.01  --bmc1_unsat_core_children              false
% 1.17/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/1.01  --bmc1_out_stat                         full
% 1.17/1.01  --bmc1_ground_init                      false
% 1.17/1.01  --bmc1_pre_inst_next_state              false
% 1.17/1.01  --bmc1_pre_inst_state                   false
% 1.17/1.01  --bmc1_pre_inst_reach_state             false
% 1.17/1.01  --bmc1_out_unsat_core                   false
% 1.17/1.01  --bmc1_aig_witness_out                  false
% 1.17/1.01  --bmc1_verbose                          false
% 1.17/1.01  --bmc1_dump_clauses_tptp                false
% 1.17/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.17/1.01  --bmc1_dump_file                        -
% 1.17/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.17/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.17/1.01  --bmc1_ucm_extend_mode                  1
% 1.17/1.01  --bmc1_ucm_init_mode                    2
% 1.17/1.01  --bmc1_ucm_cone_mode                    none
% 1.17/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.17/1.01  --bmc1_ucm_relax_model                  4
% 1.17/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.17/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/1.01  --bmc1_ucm_layered_model                none
% 1.17/1.01  --bmc1_ucm_max_lemma_size               10
% 1.17/1.01  
% 1.17/1.01  ------ AIG Options
% 1.17/1.01  
% 1.17/1.01  --aig_mode                              false
% 1.17/1.01  
% 1.17/1.01  ------ Instantiation Options
% 1.17/1.01  
% 1.17/1.01  --instantiation_flag                    true
% 1.17/1.01  --inst_sos_flag                         false
% 1.17/1.01  --inst_sos_phase                        true
% 1.17/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/1.01  --inst_lit_sel_side                     none
% 1.17/1.01  --inst_solver_per_active                1400
% 1.17/1.01  --inst_solver_calls_frac                1.
% 1.17/1.01  --inst_passive_queue_type               priority_queues
% 1.17/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/1.01  --inst_passive_queues_freq              [25;2]
% 1.17/1.01  --inst_dismatching                      true
% 1.17/1.01  --inst_eager_unprocessed_to_passive     true
% 1.17/1.01  --inst_prop_sim_given                   true
% 1.17/1.01  --inst_prop_sim_new                     false
% 1.17/1.01  --inst_subs_new                         false
% 1.17/1.01  --inst_eq_res_simp                      false
% 1.17/1.01  --inst_subs_given                       false
% 1.17/1.01  --inst_orphan_elimination               true
% 1.17/1.01  --inst_learning_loop_flag               true
% 1.17/1.01  --inst_learning_start                   3000
% 1.17/1.01  --inst_learning_factor                  2
% 1.17/1.01  --inst_start_prop_sim_after_learn       3
% 1.17/1.01  --inst_sel_renew                        solver
% 1.17/1.01  --inst_lit_activity_flag                true
% 1.17/1.01  --inst_restr_to_given                   false
% 1.17/1.01  --inst_activity_threshold               500
% 1.17/1.01  --inst_out_proof                        true
% 1.17/1.01  
% 1.17/1.01  ------ Resolution Options
% 1.17/1.01  
% 1.17/1.01  --resolution_flag                       false
% 1.17/1.01  --res_lit_sel                           adaptive
% 1.17/1.01  --res_lit_sel_side                      none
% 1.17/1.01  --res_ordering                          kbo
% 1.17/1.01  --res_to_prop_solver                    active
% 1.17/1.01  --res_prop_simpl_new                    false
% 1.17/1.01  --res_prop_simpl_given                  true
% 1.17/1.01  --res_passive_queue_type                priority_queues
% 1.17/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/1.01  --res_passive_queues_freq               [15;5]
% 1.17/1.01  --res_forward_subs                      full
% 1.17/1.01  --res_backward_subs                     full
% 1.17/1.01  --res_forward_subs_resolution           true
% 1.17/1.01  --res_backward_subs_resolution          true
% 1.17/1.01  --res_orphan_elimination                true
% 1.17/1.01  --res_time_limit                        2.
% 1.17/1.01  --res_out_proof                         true
% 1.17/1.01  
% 1.17/1.01  ------ Superposition Options
% 1.17/1.01  
% 1.17/1.01  --superposition_flag                    false
% 1.17/1.01  --sup_passive_queue_type                priority_queues
% 1.17/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.17/1.01  --demod_completeness_check              fast
% 1.17/1.01  --demod_use_ground                      true
% 1.17/1.01  --sup_to_prop_solver                    passive
% 1.17/1.01  --sup_prop_simpl_new                    true
% 1.17/1.01  --sup_prop_simpl_given                  true
% 1.17/1.01  --sup_fun_splitting                     false
% 1.17/1.01  --sup_smt_interval                      50000
% 1.17/1.01  
% 1.17/1.01  ------ Superposition Simplification Setup
% 1.17/1.01  
% 1.17/1.01  --sup_indices_passive                   []
% 1.17/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_full_bw                           [BwDemod]
% 1.17/1.01  --sup_immed_triv                        [TrivRules]
% 1.17/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_immed_bw_main                     []
% 1.17/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.01  
% 1.17/1.01  ------ Combination Options
% 1.17/1.01  
% 1.17/1.01  --comb_res_mult                         3
% 1.17/1.01  --comb_sup_mult                         2
% 1.17/1.01  --comb_inst_mult                        10
% 1.17/1.01  
% 1.17/1.01  ------ Debug Options
% 1.17/1.01  
% 1.17/1.01  --dbg_backtrace                         false
% 1.17/1.01  --dbg_dump_prop_clauses                 false
% 1.17/1.01  --dbg_dump_prop_clauses_file            -
% 1.17/1.01  --dbg_out_stat                          false
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  ------ Proving...
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  % SZS status Theorem for theBenchmark.p
% 1.17/1.01  
% 1.17/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.17/1.01  
% 1.17/1.01  fof(f6,axiom,(
% 1.17/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f18,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/1.01    inference(ennf_transformation,[],[f6])).
% 1.17/1.01  
% 1.17/1.01  fof(f19,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(flattening,[],[f18])).
% 1.17/1.01  
% 1.17/1.01  fof(f27,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(nnf_transformation,[],[f19])).
% 1.17/1.01  
% 1.17/1.01  fof(f28,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(rectify,[],[f27])).
% 1.17/1.01  
% 1.17/1.01  fof(f29,plain,(
% 1.17/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f30,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 1.17/1.01  
% 1.17/1.01  fof(f52,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f30])).
% 1.17/1.01  
% 1.17/1.01  fof(f4,axiom,(
% 1.17/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f14,plain,(
% 1.17/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/1.01    inference(ennf_transformation,[],[f4])).
% 1.17/1.01  
% 1.17/1.01  fof(f15,plain,(
% 1.17/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(flattening,[],[f14])).
% 1.17/1.01  
% 1.17/1.01  fof(f47,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f15])).
% 1.17/1.01  
% 1.17/1.01  fof(f7,conjecture,(
% 1.17/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => ~r1_xboole_0(X3,X1))))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f8,negated_conjecture,(
% 1.17/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => ~r1_xboole_0(X3,X1))))))),
% 1.17/1.01    inference(negated_conjecture,[],[f7])).
% 1.17/1.01  
% 1.17/1.01  fof(f20,plain,(
% 1.17/1.01    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <~> ! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.17/1.01    inference(ennf_transformation,[],[f8])).
% 1.17/1.01  
% 1.17/1.01  fof(f21,plain,(
% 1.17/1.01    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <~> ! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/1.01    inference(flattening,[],[f20])).
% 1.17/1.01  
% 1.17/1.01  fof(f31,plain,(
% 1.17/1.01    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/1.01    inference(nnf_transformation,[],[f21])).
% 1.17/1.01  
% 1.17/1.01  fof(f32,plain,(
% 1.17/1.01    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X3] : (~r1_xboole_0(X3,X1) | ~m1_connsp_2(X3,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/1.01    inference(flattening,[],[f31])).
% 1.17/1.01  
% 1.17/1.01  fof(f33,plain,(
% 1.17/1.01    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/1.01    inference(rectify,[],[f32])).
% 1.17/1.01  
% 1.17/1.01  fof(f37,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) => (r1_xboole_0(sK5,X1) & m1_connsp_2(sK5,X0,X2))) )),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f36,plain,(
% 1.17/1.01    ( ! [X0,X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) => ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,sK4)) | ~r2_hidden(sK4,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,X0,sK4)) | r2_hidden(sK4,k2_pre_topc(X0,X1))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f35,plain,(
% 1.17/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : ((? [X3] : (r1_xboole_0(X3,sK3) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,sK3))) & (! [X4] : (~r1_xboole_0(X4,sK3) | ~m1_connsp_2(X4,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,sK3))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f34,plain,(
% 1.17/1.01    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,X0,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,X0,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X3,X1) & m1_connsp_2(X3,sK2,X2)) | ~r2_hidden(X2,k2_pre_topc(sK2,X1))) & (! [X4] : (~r1_xboole_0(X4,X1) | ~m1_connsp_2(X4,sK2,X2)) | r2_hidden(X2,k2_pre_topc(sK2,X1))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f38,plain,(
% 1.17/1.01    ((((r1_xboole_0(sK5,sK3) & m1_connsp_2(sK5,sK2,sK4)) | ~r2_hidden(sK4,k2_pre_topc(sK2,sK3))) & (! [X4] : (~r1_xboole_0(X4,sK3) | ~m1_connsp_2(X4,sK2,sK4)) | r2_hidden(sK4,k2_pre_topc(sK2,sK3))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.17/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f37,f36,f35,f34])).
% 1.17/1.01  
% 1.17/1.01  fof(f55,plain,(
% 1.17/1.01    v2_pre_topc(sK2)),
% 1.17/1.01    inference(cnf_transformation,[],[f38])).
% 1.17/1.01  
% 1.17/1.01  fof(f54,plain,(
% 1.17/1.01    ~v2_struct_0(sK2)),
% 1.17/1.01    inference(cnf_transformation,[],[f38])).
% 1.17/1.01  
% 1.17/1.01  fof(f56,plain,(
% 1.17/1.01    l1_pre_topc(sK2)),
% 1.17/1.01    inference(cnf_transformation,[],[f38])).
% 1.17/1.01  
% 1.17/1.01  fof(f3,axiom,(
% 1.17/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f12,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/1.01    inference(ennf_transformation,[],[f3])).
% 1.17/1.01  
% 1.17/1.01  fof(f13,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/1.01    inference(flattening,[],[f12])).
% 1.17/1.01  
% 1.17/1.01  fof(f22,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/1.01    inference(nnf_transformation,[],[f13])).
% 1.17/1.01  
% 1.17/1.01  fof(f23,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/1.01    inference(flattening,[],[f22])).
% 1.17/1.01  
% 1.17/1.01  fof(f24,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/1.01    inference(rectify,[],[f23])).
% 1.17/1.01  
% 1.17/1.01  fof(f25,plain,(
% 1.17/1.01    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK0(X0,X1,X2)) & r2_hidden(X2,sK0(X0,X1,X2)) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f26,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK0(X0,X1,X2)) & r2_hidden(X2,sK0(X0,X1,X2)) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 1.17/1.01  
% 1.17/1.01  fof(f42,plain,(
% 1.17/1.01    ( ! [X4,X2,X0,X1] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f26])).
% 1.17/1.01  
% 1.17/1.01  fof(f49,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f30])).
% 1.17/1.01  
% 1.17/1.01  fof(f50,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f30])).
% 1.17/1.01  
% 1.17/1.01  fof(f1,axiom,(
% 1.17/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f9,plain,(
% 1.17/1.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.17/1.01    inference(ennf_transformation,[],[f1])).
% 1.17/1.01  
% 1.17/1.01  fof(f39,plain,(
% 1.17/1.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f9])).
% 1.17/1.01  
% 1.17/1.01  fof(f5,axiom,(
% 1.17/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f16,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/1.01    inference(ennf_transformation,[],[f5])).
% 1.17/1.01  
% 1.17/1.01  fof(f17,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(flattening,[],[f16])).
% 1.17/1.01  
% 1.17/1.01  fof(f48,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f17])).
% 1.17/1.01  
% 1.17/1.01  fof(f59,plain,(
% 1.17/1.01    ( ! [X4] : (~r1_xboole_0(X4,sK3) | ~m1_connsp_2(X4,sK2,sK4) | r2_hidden(sK4,k2_pre_topc(sK2,sK3))) )),
% 1.17/1.01    inference(cnf_transformation,[],[f38])).
% 1.17/1.01  
% 1.17/1.01  fof(f2,axiom,(
% 1.17/1.01    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f10,plain,(
% 1.17/1.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.17/1.01    inference(ennf_transformation,[],[f2])).
% 1.17/1.01  
% 1.17/1.01  fof(f11,plain,(
% 1.17/1.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.17/1.01    inference(flattening,[],[f10])).
% 1.17/1.01  
% 1.17/1.01  fof(f40,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f11])).
% 1.17/1.01  
% 1.17/1.01  fof(f51,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f30])).
% 1.17/1.01  
% 1.17/1.01  fof(f45,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r2_hidden(X2,sK0(X0,X1,X2)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f26])).
% 1.17/1.01  
% 1.17/1.01  fof(f46,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r1_xboole_0(X1,sK0(X0,X1,X2)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f26])).
% 1.17/1.01  
% 1.17/1.01  fof(f43,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f26])).
% 1.17/1.01  
% 1.17/1.01  fof(f44,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | v3_pre_topc(sK0(X0,X1,X2),X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f26])).
% 1.17/1.01  
% 1.17/1.01  fof(f61,plain,(
% 1.17/1.01    r1_xboole_0(sK5,sK3) | ~r2_hidden(sK4,k2_pre_topc(sK2,sK3))),
% 1.17/1.01    inference(cnf_transformation,[],[f38])).
% 1.17/1.01  
% 1.17/1.01  fof(f60,plain,(
% 1.17/1.01    m1_connsp_2(sK5,sK2,sK4) | ~r2_hidden(sK4,k2_pre_topc(sK2,sK3))),
% 1.17/1.01    inference(cnf_transformation,[],[f38])).
% 1.17/1.01  
% 1.17/1.01  fof(f58,plain,(
% 1.17/1.01    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.17/1.01    inference(cnf_transformation,[],[f38])).
% 1.17/1.01  
% 1.17/1.01  fof(f57,plain,(
% 1.17/1.01    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.17/1.01    inference(cnf_transformation,[],[f38])).
% 1.17/1.01  
% 1.17/1.01  cnf(c_11,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | r2_hidden(X2,sK1(X1,X2,X0))
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_8,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_148,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | r2_hidden(X2,sK1(X1,X2,X0))
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_11,c_8]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_21,negated_conjecture,
% 1.17/1.01      ( v2_pre_topc(sK2) ),
% 1.17/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_338,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1,sK1(sK2,X1,X0))
% 1.17/1.01      | ~ l1_pre_topc(sK2)
% 1.17/1.01      | v2_struct_0(sK2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_148,c_21]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_22,negated_conjecture,
% 1.17/1.01      ( ~ v2_struct_0(sK2) ),
% 1.17/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_20,negated_conjecture,
% 1.17/1.01      ( l1_pre_topc(sK2) ),
% 1.17/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_342,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1,sK1(sK2,X1,X0)) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_338,c_22,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1124,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0_46,sK2,X1_46)
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1_46,sK1(sK2,X1_46,X0_46)) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_342]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1245,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0_46,sK2,sK4)
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(sK4,sK1(sK2,sK4,X0_46)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1124]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1500,plain,
% 1.17/1.01      ( ~ m1_connsp_2(sK5,sK2,sK4)
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(sK4,sK1(sK2,sK4,sK5)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1245]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1501,plain,
% 1.17/1.01      ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,sK1(sK2,sK4,sK5)) = iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_6,plain,
% 1.17/1.01      ( ~ v3_pre_topc(X0,X1)
% 1.17/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.17/1.01      | ~ r2_hidden(X3,X0)
% 1.17/1.01      | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
% 1.17/1.01      | ~ r1_xboole_0(X2,X0)
% 1.17/1.01      | ~ l1_pre_topc(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_581,plain,
% 1.17/1.01      ( ~ v3_pre_topc(X0,sK2)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.17/1.01      | ~ r2_hidden(X2,X0)
% 1.17/1.01      | ~ r2_hidden(X2,k2_pre_topc(sK2,X1))
% 1.17/1.01      | ~ r1_xboole_0(X1,X0) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_6,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1117,plain,
% 1.17/1.01      ( ~ v3_pre_topc(X0_46,sK2)
% 1.17/1.01      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 1.17/1.01      | ~ r2_hidden(X2_46,X0_46)
% 1.17/1.01      | ~ r2_hidden(X2_46,k2_pre_topc(sK2,X1_46))
% 1.17/1.01      | ~ r1_xboole_0(X1_46,X0_46) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_581]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1270,plain,
% 1.17/1.01      ( ~ v3_pre_topc(sK1(sK2,sK4,X0_46),sK2)
% 1.17/1.01      | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X2_46,u1_struct_0(sK2))
% 1.17/1.01      | ~ m1_subset_1(sK1(sK2,sK4,X0_46),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ r2_hidden(X2_46,sK1(sK2,sK4,X0_46))
% 1.17/1.01      | ~ r2_hidden(X2_46,k2_pre_topc(sK2,X1_46))
% 1.17/1.01      | ~ r1_xboole_0(X1_46,sK1(sK2,sK4,X0_46)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1117]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1362,plain,
% 1.17/1.01      ( ~ v3_pre_topc(sK1(sK2,sK4,X0_46),sK2)
% 1.17/1.01      | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK1(sK2,sK4,X0_46),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | ~ r2_hidden(sK4,sK1(sK2,sK4,X0_46))
% 1.17/1.01      | ~ r2_hidden(sK4,k2_pre_topc(sK2,X1_46))
% 1.17/1.01      | ~ r1_xboole_0(X1_46,sK1(sK2,sK4,X0_46)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1270]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1428,plain,
% 1.17/1.01      ( ~ v3_pre_topc(sK1(sK2,sK4,sK5),sK2)
% 1.17/1.01      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | ~ r2_hidden(sK4,sK1(sK2,sK4,sK5))
% 1.17/1.01      | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_46))
% 1.17/1.01      | ~ r1_xboole_0(X0_46,sK1(sK2,sK4,sK5)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1362]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1432,plain,
% 1.17/1.01      ( v3_pre_topc(sK1(sK2,sK4,sK5),sK2) != iProver_top
% 1.17/1.01      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,sK1(sK2,sK4,sK5)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) != iProver_top
% 1.17/1.01      | r1_xboole_0(X0_46,sK1(sK2,sK4,sK5)) != iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1428]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1434,plain,
% 1.17/1.01      ( v3_pre_topc(sK1(sK2,sK4,sK5),sK2) != iProver_top
% 1.17/1.01      | m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,sK1(sK2,sK4,sK5)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
% 1.17/1.01      | r1_xboole_0(sK3,sK1(sK2,sK4,sK5)) != iProver_top ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1432]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_14,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_127,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_14,c_8]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_398,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ l1_pre_topc(sK2)
% 1.17/1.01      | v2_struct_0(sK2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_127,c_21]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_402,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | m1_subset_1(sK1(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_398,c_22,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1122,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0_46,sK2,X1_46)
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 1.17/1.01      | m1_subset_1(sK1(sK2,X1_46,X0_46),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_402]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1225,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0_46,sK2,sK4)
% 1.17/1.01      | m1_subset_1(sK1(sK2,sK4,X0_46),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1122]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1406,plain,
% 1.17/1.01      ( ~ m1_connsp_2(sK5,sK2,sK4)
% 1.17/1.01      | m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1225]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1407,plain,
% 1.17/1.01      ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
% 1.17/1.01      | m1_subset_1(sK1(sK2,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1406]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_13,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_134,plain,
% 1.17/1.01      ( v3_pre_topc(sK1(X1,X2,X0),X1)
% 1.17/1.01      | ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_13,c_8]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_135,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(renaming,[status(thm)],[c_134]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_378,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | v3_pre_topc(sK1(sK2,X1,X0),sK2)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | ~ l1_pre_topc(sK2)
% 1.17/1.01      | v2_struct_0(sK2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_135,c_21]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_382,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | v3_pre_topc(sK1(sK2,X1,X0),sK2)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_378,c_22,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1123,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0_46,sK2,X1_46)
% 1.17/1.01      | v3_pre_topc(sK1(sK2,X1_46,X0_46),sK2)
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2)) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_382]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1230,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0_46,sK2,sK4)
% 1.17/1.01      | v3_pre_topc(sK1(sK2,sK4,X0_46),sK2)
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1123]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1391,plain,
% 1.17/1.01      ( ~ m1_connsp_2(sK5,sK2,sK4)
% 1.17/1.01      | v3_pre_topc(sK1(sK2,sK4,sK5),sK2)
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1230]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1392,plain,
% 1.17/1.01      ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
% 1.17/1.01      | v3_pre_topc(sK1(sK2,sK4,sK5),sK2) = iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_0,plain,
% 1.17/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 1.17/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1130,plain,
% 1.17/1.01      ( ~ r1_xboole_0(X0_46,X1_46) | r1_xboole_0(X1_46,X0_46) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1303,plain,
% 1.17/1.01      ( r1_xboole_0(X0_46,sK1(sK2,sK4,X1_46))
% 1.17/1.01      | ~ r1_xboole_0(sK1(sK2,sK4,X1_46),X0_46) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1130]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1386,plain,
% 1.17/1.01      ( r1_xboole_0(X0_46,sK1(sK2,sK4,sK5))
% 1.17/1.01      | ~ r1_xboole_0(sK1(sK2,sK4,sK5),X0_46) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1303]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1387,plain,
% 1.17/1.01      ( r1_xboole_0(X0_46,sK1(sK2,sK4,sK5)) = iProver_top
% 1.17/1.01      | r1_xboole_0(sK1(sK2,sK4,sK5),X0_46) != iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1386]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1389,plain,
% 1.17/1.01      ( r1_xboole_0(sK1(sK2,sK4,sK5),sK3) != iProver_top
% 1.17/1.01      | r1_xboole_0(sK3,sK1(sK2,sK4,sK5)) = iProver_top ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1387]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_9,plain,
% 1.17/1.01      ( m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | ~ v3_pre_topc(X0,X1)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | ~ r2_hidden(X2,X0)
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_450,plain,
% 1.17/1.01      ( m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | ~ v3_pre_topc(X0,sK2)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | ~ r2_hidden(X1,X0)
% 1.17/1.01      | ~ l1_pre_topc(sK2)
% 1.17/1.01      | v2_struct_0(sK2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_9,c_21]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_454,plain,
% 1.17/1.01      ( m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | ~ v3_pre_topc(X0,sK2)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | ~ r2_hidden(X1,X0) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_450,c_22,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1121,plain,
% 1.17/1.01      ( m1_connsp_2(X0_46,sK2,X1_46)
% 1.17/1.01      | ~ v3_pre_topc(X0_46,sK2)
% 1.17/1.01      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 1.17/1.01      | ~ r2_hidden(X1_46,X0_46) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_454]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1281,plain,
% 1.17/1.01      ( m1_connsp_2(sK0(sK2,X0_46,sK4),sK2,X1_46)
% 1.17/1.01      | ~ v3_pre_topc(sK0(sK2,X0_46,sK4),sK2)
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 1.17/1.01      | ~ m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ r2_hidden(X1_46,sK0(sK2,X0_46,sK4)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1121]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1357,plain,
% 1.17/1.01      ( m1_connsp_2(sK0(sK2,X0_46,sK4),sK2,sK4)
% 1.17/1.01      | ~ v3_pre_topc(sK0(sK2,X0_46,sK4),sK2)
% 1.17/1.01      | ~ m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | ~ r2_hidden(sK4,sK0(sK2,X0_46,sK4)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1281]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1358,plain,
% 1.17/1.01      ( m1_connsp_2(sK0(sK2,X0_46,sK4),sK2,sK4) = iProver_top
% 1.17/1.01      | v3_pre_topc(sK0(sK2,X0_46,sK4),sK2) != iProver_top
% 1.17/1.01      | m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,sK0(sK2,X0_46,sK4)) != iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1357]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1360,plain,
% 1.17/1.01      ( m1_connsp_2(sK0(sK2,sK3,sK4),sK2,sK4) = iProver_top
% 1.17/1.01      | v3_pre_topc(sK0(sK2,sK3,sK4),sK2) != iProver_top
% 1.17/1.01      | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,sK0(sK2,sK3,sK4)) != iProver_top ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1358]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_17,negated_conjecture,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,sK4)
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
% 1.17/1.01      | ~ r1_xboole_0(X0,sK3) ),
% 1.17/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1127,negated_conjecture,
% 1.17/1.01      ( ~ m1_connsp_2(X0_46,sK2,sK4)
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
% 1.17/1.01      | ~ r1_xboole_0(X0_46,sK3) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1330,plain,
% 1.17/1.01      ( ~ m1_connsp_2(sK0(sK2,sK3,sK4),sK2,sK4)
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
% 1.17/1.01      | ~ r1_xboole_0(sK0(sK2,sK3,sK4),sK3) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1127]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1333,plain,
% 1.17/1.01      ( m1_connsp_2(sK0(sK2,sK3,sK4),sK2,sK4) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
% 1.17/1.01      | r1_xboole_0(sK0(sK2,sK3,sK4),sK3) != iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1,plain,
% 1.17/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 1.17/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_12,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | r1_tarski(sK1(X1,X2,X0),X0)
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_141,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | r1_tarski(sK1(X1,X2,X0),X0)
% 1.17/1.01      | ~ v2_pre_topc(X1)
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_12,c_8]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_358,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r1_tarski(sK1(sK2,X1,X0),X0)
% 1.17/1.01      | ~ l1_pre_topc(sK2)
% 1.17/1.01      | v2_struct_0(sK2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_141,c_21]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_362,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r1_tarski(sK1(sK2,X1,X0),X0) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_358,c_22,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_530,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | ~ r1_xboole_0(X0,X2)
% 1.17/1.01      | r1_xboole_0(sK1(sK2,X1,X0),X2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_1,c_362]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1119,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0_46,sK2,X1_46)
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 1.17/1.01      | ~ r1_xboole_0(X0_46,X2_46)
% 1.17/1.01      | r1_xboole_0(sK1(sK2,X1_46,X0_46),X2_46) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_530]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1260,plain,
% 1.17/1.01      ( ~ m1_connsp_2(X0_46,sK2,sK4)
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | ~ r1_xboole_0(X0_46,X1_46)
% 1.17/1.01      | r1_xboole_0(sK1(sK2,sK4,X0_46),X1_46) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1119]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1323,plain,
% 1.17/1.01      ( ~ m1_connsp_2(sK5,sK2,sK4)
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | r1_xboole_0(sK1(sK2,sK4,sK5),X0_46)
% 1.17/1.01      | ~ r1_xboole_0(sK5,X0_46) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1260]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1324,plain,
% 1.17/1.01      ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r1_xboole_0(sK1(sK2,sK4,sK5),X0_46) = iProver_top
% 1.17/1.01      | r1_xboole_0(sK5,X0_46) != iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1326,plain,
% 1.17/1.01      ( m1_connsp_2(sK5,sK2,sK4) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r1_xboole_0(sK1(sK2,sK4,sK5),sK3) = iProver_top
% 1.17/1.01      | r1_xboole_0(sK5,sK3) != iProver_top ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1324]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1290,plain,
% 1.17/1.01      ( ~ r1_xboole_0(X0_46,sK0(sK2,X0_46,sK4))
% 1.17/1.01      | r1_xboole_0(sK0(sK2,X0_46,sK4),X0_46) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1130]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1291,plain,
% 1.17/1.01      ( r1_xboole_0(X0_46,sK0(sK2,X0_46,sK4)) != iProver_top
% 1.17/1.01      | r1_xboole_0(sK0(sK2,X0_46,sK4),X0_46) = iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1290]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1293,plain,
% 1.17/1.01      ( r1_xboole_0(sK0(sK2,sK3,sK4),sK3) = iProver_top
% 1.17/1.01      | r1_xboole_0(sK3,sK0(sK2,sK3,sK4)) != iProver_top ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1291]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_3,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | r2_hidden(X2,sK0(X1,X0,X2))
% 1.17/1.01      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_630,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1,sK0(sK2,X0,X1))
% 1.17/1.01      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 1.17/1.01      | v2_struct_0(sK2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_3,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_634,plain,
% 1.17/1.01      ( r2_hidden(X1,k2_pre_topc(sK2,X0))
% 1.17/1.01      | r2_hidden(X1,sK0(sK2,X0,X1))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_630,c_22]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_635,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1,sK0(sK2,X0,X1))
% 1.17/1.01      | r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
% 1.17/1.01      inference(renaming,[status(thm)],[c_634]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1115,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1_46,sK0(sK2,X0_46,X1_46))
% 1.17/1.01      | r2_hidden(X1_46,k2_pre_topc(sK2,X0_46)) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_635]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1255,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(sK4,sK0(sK2,X0_46,sK4))
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1115]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1256,plain,
% 1.17/1.01      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,sK0(sK2,X0_46,sK4)) = iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) = iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1255]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1258,plain,
% 1.17/1.01      ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,sK0(sK2,sK3,sK4)) = iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1256]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_2,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.17/1.01      | r1_xboole_0(X0,sK0(X1,X0,X2))
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_653,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 1.17/1.01      | r1_xboole_0(X0,sK0(sK2,X0,X1))
% 1.17/1.01      | v2_struct_0(sK2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_2,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_657,plain,
% 1.17/1.01      ( r1_xboole_0(X0,sK0(sK2,X0,X1))
% 1.17/1.01      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_653,c_22]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_658,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 1.17/1.01      | r1_xboole_0(X0,sK0(sK2,X0,X1)) ),
% 1.17/1.01      inference(renaming,[status(thm)],[c_657]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1114,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1_46,k2_pre_topc(sK2,X0_46))
% 1.17/1.01      | r1_xboole_0(X0_46,sK0(sK2,X0_46,X1_46)) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_658]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1250,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,X0_46))
% 1.17/1.01      | r1_xboole_0(X0_46,sK0(sK2,X0_46,sK4)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1114]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1251,plain,
% 1.17/1.01      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) = iProver_top
% 1.17/1.01      | r1_xboole_0(X0_46,sK0(sK2,X0_46,sK4)) = iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1250]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1253,plain,
% 1.17/1.01      ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
% 1.17/1.01      | r1_xboole_0(sK3,sK0(sK2,sK3,sK4)) = iProver_top ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1251]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_5,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.17/1.01      | m1_subset_1(sK0(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.01      | r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.17/1.01      | ~ l1_pre_topc(X1)
% 1.17/1.01      | v2_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_607,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | m1_subset_1(sK0(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 1.17/1.01      | v2_struct_0(sK2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_5,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_611,plain,
% 1.17/1.01      ( r2_hidden(X1,k2_pre_topc(sK2,X0))
% 1.17/1.01      | m1_subset_1(sK0(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_607,c_22]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_612,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | m1_subset_1(sK0(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
% 1.17/1.01      inference(renaming,[status(thm)],[c_611]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1116,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 1.17/1.01      | m1_subset_1(sK0(sK2,X0_46,X1_46),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | r2_hidden(X1_46,k2_pre_topc(sK2,X0_46)) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_612]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1240,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1116]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1241,plain,
% 1.17/1.01      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | m1_subset_1(sK0(sK2,X0_46,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) = iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1243,plain,
% 1.17/1.01      ( m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1241]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_4,plain,
% 1.17/1.01      ( v3_pre_topc(sK0(X0,X1,X2),X0)
% 1.17/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.01      | r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.17/1.01      | ~ l1_pre_topc(X0)
% 1.17/1.01      | v2_struct_0(X0) ),
% 1.17/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_676,plain,
% 1.17/1.01      ( v3_pre_topc(sK0(sK2,X0,X1),sK2)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1,k2_pre_topc(sK2,X0))
% 1.17/1.01      | v2_struct_0(sK2) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_4,c_20]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_680,plain,
% 1.17/1.01      ( r2_hidden(X1,k2_pre_topc(sK2,X0))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | v3_pre_topc(sK0(sK2,X0,X1),sK2) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_676,c_22]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_681,plain,
% 1.17/1.01      ( v3_pre_topc(sK0(sK2,X0,X1),sK2)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
% 1.17/1.01      inference(renaming,[status(thm)],[c_680]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1113,plain,
% 1.17/1.01      ( v3_pre_topc(sK0(sK2,X0_46,X1_46),sK2)
% 1.17/1.01      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(X1_46,k2_pre_topc(sK2,X0_46)) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_681]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1235,plain,
% 1.17/1.01      ( v3_pre_topc(sK0(sK2,X0_46,sK4),sK2)
% 1.17/1.01      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.17/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1113]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1236,plain,
% 1.17/1.01      ( v3_pre_topc(sK0(sK2,X0_46,sK4),sK2) = iProver_top
% 1.17/1.01      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,X0_46)) = iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_1235]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1238,plain,
% 1.17/1.01      ( v3_pre_topc(sK0(sK2,sK3,sK4),sK2) = iProver_top
% 1.17/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 1.17/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_1236]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_15,negated_conjecture,
% 1.17/1.01      ( ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) | r1_xboole_0(sK5,sK3) ),
% 1.17/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_32,plain,
% 1.17/1.01      ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
% 1.17/1.01      | r1_xboole_0(sK5,sK3) = iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_16,negated_conjecture,
% 1.17/1.01      ( m1_connsp_2(sK5,sK2,sK4)
% 1.17/1.01      | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
% 1.17/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_31,plain,
% 1.17/1.01      ( m1_connsp_2(sK5,sK2,sK4) = iProver_top
% 1.17/1.01      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_18,negated_conjecture,
% 1.17/1.01      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.17/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_27,plain,
% 1.17/1.01      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_19,negated_conjecture,
% 1.17/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.17/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_26,plain,
% 1.17/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.17/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(contradiction,plain,
% 1.17/1.01      ( $false ),
% 1.17/1.01      inference(minisat,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_1501,c_1434,c_1407,c_1392,c_1389,c_1360,c_1333,c_1326,
% 1.17/1.01                 c_1293,c_1258,c_1253,c_1243,c_1238,c_32,c_31,c_27,c_26]) ).
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.17/1.01  
% 1.17/1.01  ------                               Statistics
% 1.17/1.01  
% 1.17/1.01  ------ General
% 1.17/1.01  
% 1.17/1.01  abstr_ref_over_cycles:                  0
% 1.17/1.01  abstr_ref_under_cycles:                 0
% 1.17/1.01  gc_basic_clause_elim:                   0
% 1.17/1.01  forced_gc_time:                         0
% 1.17/1.01  parsing_time:                           0.009
% 1.17/1.01  unif_index_cands_time:                  0.
% 1.17/1.01  unif_index_add_time:                    0.
% 1.17/1.01  orderings_time:                         0.
% 1.17/1.01  out_proof_time:                         0.015
% 1.17/1.01  total_time:                             0.085
% 1.17/1.01  num_of_symbols:                         49
% 1.17/1.01  num_of_terms:                           1267
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing
% 1.17/1.01  
% 1.17/1.01  num_of_splits:                          0
% 1.17/1.01  num_of_split_atoms:                     0
% 1.17/1.01  num_of_reused_defs:                     0
% 1.17/1.01  num_eq_ax_congr_red:                    0
% 1.17/1.01  num_of_sem_filtered_clauses:            0
% 1.17/1.01  num_of_subtypes:                        3
% 1.17/1.01  monotx_restored_types:                  0
% 1.17/1.01  sat_num_of_epr_types:                   0
% 1.17/1.01  sat_num_of_non_cyclic_types:            0
% 1.17/1.01  sat_guarded_non_collapsed_types:        0
% 1.17/1.01  num_pure_diseq_elim:                    0
% 1.17/1.01  simp_replaced_by:                       0
% 1.17/1.01  res_preprocessed:                       41
% 1.17/1.01  prep_upred:                             0
% 1.17/1.01  prep_unflattend:                        0
% 1.17/1.01  smt_new_axioms:                         0
% 1.17/1.01  pred_elim_cands:                        5
% 1.17/1.01  pred_elim:                              4
% 1.17/1.01  pred_elim_cl:                           5
% 1.17/1.01  pred_elim_cycles:                       7
% 1.17/1.01  merged_defs:                            0
% 1.17/1.01  merged_defs_ncl:                        0
% 1.17/1.01  bin_hyper_res:                          0
% 1.17/1.01  prep_cycles:                            2
% 1.17/1.01  pred_elim_time:                         0.016
% 1.17/1.01  splitting_time:                         0.
% 1.17/1.01  sem_filter_time:                        0.
% 1.17/1.01  monotx_time:                            0.
% 1.17/1.01  subtype_inf_time:                       0.001
% 1.17/1.01  
% 1.17/1.01  ------ Problem properties
% 1.17/1.01  
% 1.17/1.01  clauses:                                18
% 1.17/1.01  conjectures:                            5
% 1.17/1.01  epr:                                    1
% 1.17/1.01  horn:                                   14
% 1.17/1.01  ground:                                 4
% 1.17/1.01  unary:                                  2
% 1.17/1.01  binary:                                 3
% 1.17/1.01  lits:                                   60
% 1.17/1.01  lits_eq:                                0
% 1.17/1.01  fd_pure:                                0
% 1.17/1.01  fd_pseudo:                              0
% 1.17/1.01  fd_cond:                                0
% 1.17/1.01  fd_pseudo_cond:                         0
% 1.17/1.01  ac_symbols:                             0
% 1.17/1.01  
% 1.17/1.01  ------ Propositional Solver
% 1.17/1.01  
% 1.17/1.01  prop_solver_calls:                      17
% 1.17/1.01  prop_fast_solver_calls:                 605
% 1.17/1.01  smt_solver_calls:                       0
% 1.17/1.01  smt_fast_solver_calls:                  0
% 1.17/1.01  prop_num_of_clauses:                    458
% 1.17/1.01  prop_preprocess_simplified:             1676
% 1.17/1.01  prop_fo_subsumed:                       32
% 1.17/1.01  prop_solver_time:                       0.
% 1.17/1.01  smt_solver_time:                        0.
% 1.17/1.01  smt_fast_solver_time:                   0.
% 1.17/1.01  prop_fast_solver_time:                  0.
% 1.17/1.01  prop_unsat_core_time:                   0.
% 1.17/1.01  
% 1.17/1.01  ------ QBF
% 1.17/1.01  
% 1.17/1.01  qbf_q_res:                              0
% 1.17/1.01  qbf_num_tautologies:                    0
% 1.17/1.01  qbf_prep_cycles:                        0
% 1.17/1.01  
% 1.17/1.01  ------ BMC1
% 1.17/1.01  
% 1.17/1.01  bmc1_current_bound:                     -1
% 1.17/1.01  bmc1_last_solved_bound:                 -1
% 1.17/1.01  bmc1_unsat_core_size:                   -1
% 1.17/1.01  bmc1_unsat_core_parents_size:           -1
% 1.17/1.01  bmc1_merge_next_fun:                    0
% 1.17/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.17/1.01  
% 1.17/1.01  ------ Instantiation
% 1.17/1.01  
% 1.17/1.01  inst_num_of_clauses:                    78
% 1.17/1.01  inst_num_in_passive:                    1
% 1.17/1.01  inst_num_in_active:                     67
% 1.17/1.01  inst_num_in_unprocessed:                10
% 1.17/1.01  inst_num_of_loops:                      86
% 1.17/1.01  inst_num_of_learning_restarts:          0
% 1.17/1.01  inst_num_moves_active_passive:          13
% 1.17/1.01  inst_lit_activity:                      0
% 1.17/1.01  inst_lit_activity_moves:                0
% 1.17/1.01  inst_num_tautologies:                   0
% 1.17/1.01  inst_num_prop_implied:                  0
% 1.17/1.01  inst_num_existing_simplified:           0
% 1.17/1.01  inst_num_eq_res_simplified:             0
% 1.17/1.01  inst_num_child_elim:                    0
% 1.17/1.01  inst_num_of_dismatching_blockings:      10
% 1.17/1.01  inst_num_of_non_proper_insts:           65
% 1.17/1.01  inst_num_of_duplicates:                 0
% 1.17/1.01  inst_inst_num_from_inst_to_res:         0
% 1.17/1.01  inst_dismatching_checking_time:         0.
% 1.17/1.01  
% 1.17/1.01  ------ Resolution
% 1.17/1.01  
% 1.17/1.01  res_num_of_clauses:                     0
% 1.17/1.01  res_num_in_passive:                     0
% 1.17/1.01  res_num_in_active:                      0
% 1.17/1.01  res_num_of_loops:                       43
% 1.17/1.01  res_forward_subset_subsumed:            1
% 1.17/1.01  res_backward_subset_subsumed:           0
% 1.17/1.01  res_forward_subsumed:                   0
% 1.17/1.01  res_backward_subsumed:                  0
% 1.17/1.01  res_forward_subsumption_resolution:     1
% 1.17/1.01  res_backward_subsumption_resolution:    0
% 1.17/1.01  res_clause_to_clause_subsumption:       46
% 1.17/1.01  res_orphan_elimination:                 0
% 1.17/1.01  res_tautology_del:                      2
% 1.17/1.01  res_num_eq_res_simplified:              0
% 1.17/1.01  res_num_sel_changes:                    0
% 1.17/1.01  res_moves_from_active_to_pass:          0
% 1.17/1.01  
% 1.17/1.01  ------ Superposition
% 1.17/1.01  
% 1.17/1.01  sup_time_total:                         0.
% 1.17/1.01  sup_time_generating:                    0.
% 1.17/1.01  sup_time_sim_full:                      0.
% 1.17/1.01  sup_time_sim_immed:                     0.
% 1.17/1.01  
% 1.17/1.01  sup_num_of_clauses:                     0
% 1.17/1.01  sup_num_in_active:                      0
% 1.17/1.01  sup_num_in_passive:                     0
% 1.17/1.01  sup_num_of_loops:                       0
% 1.17/1.01  sup_fw_superposition:                   0
% 1.17/1.01  sup_bw_superposition:                   0
% 1.17/1.01  sup_immediate_simplified:               0
% 1.17/1.01  sup_given_eliminated:                   0
% 1.17/1.01  comparisons_done:                       0
% 1.17/1.01  comparisons_avoided:                    0
% 1.17/1.01  
% 1.17/1.01  ------ Simplifications
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  sim_fw_subset_subsumed:                 0
% 1.17/1.01  sim_bw_subset_subsumed:                 0
% 1.17/1.01  sim_fw_subsumed:                        0
% 1.17/1.01  sim_bw_subsumed:                        0
% 1.17/1.01  sim_fw_subsumption_res:                 0
% 1.17/1.01  sim_bw_subsumption_res:                 0
% 1.17/1.01  sim_tautology_del:                      0
% 1.17/1.01  sim_eq_tautology_del:                   0
% 1.17/1.01  sim_eq_res_simp:                        0
% 1.17/1.01  sim_fw_demodulated:                     0
% 1.17/1.01  sim_bw_demodulated:                     0
% 1.17/1.01  sim_light_normalised:                   0
% 1.17/1.01  sim_joinable_taut:                      0
% 1.17/1.01  sim_joinable_simp:                      0
% 1.17/1.01  sim_ac_normalised:                      0
% 1.17/1.01  sim_smt_subsumption:                    0
% 1.17/1.01  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:16 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 160 expanded)
%              Number of clauses        :   42 (  47 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  420 (1297 expanded)
%              Number of equality atoms :   14 (  32 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

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
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_connsp_2(X3,X0,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X3) )
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_connsp_2(X3,X0,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(sK2,X0,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_connsp_2(X3,X0,sK1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,X0,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | v1_xboole_0(X3) )
                & m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_connsp_2(X3,sK0,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f28,f27,f26])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_168,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | ~ v1_xboole_0(X1_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1630,plain,
    ( ~ r2_hidden(X0_43,k1_tops_1(sK0,sK2))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_1632,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_6,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_162,plain,
    ( m1_connsp_2(X0_43,X0_44,X1_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
    | ~ r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
    | v2_struct_0(X0_44)
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1361,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_178,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | r2_hidden(X0_43,X2_43)
    | X2_43 != X1_43 ),
    theory(equality)).

cnf(c_871,plain,
    ( r2_hidden(sK1,X0_43)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | X0_43 != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_1251,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_163,plain,
    ( ~ v3_pre_topc(X0_43,X0_44)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(X1_44)))
    | ~ v2_pre_topc(X1_44)
    | ~ l1_pre_topc(X1_44)
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_172,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_163])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_158,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_948,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP2_iProver_split ),
    inference(resolution,[status(thm)],[c_172,c_158])).

cnf(c_173,plain,
    ( ~ v3_pre_topc(X0_43,X0_44)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,X0_43) = X0_43
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_163])).

cnf(c_831,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ sP3_iProver_split
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_9,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ r1_tarski(X0,sK2)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_160,negated_conjecture,
    ( ~ m1_connsp_2(X0_43,sK0,sK1)
    | ~ r1_tarski(X0_43,sK2)
    | ~ v3_pre_topc(X0_43,sK0)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_828,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_128,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_8])).

cnf(c_153,plain,
    ( ~ m1_connsp_2(X0_43,X0_44,X1_43)
    | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
    | r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
    | v2_struct_0(X0_44)
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_128])).

cnf(c_772,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_2,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_166,plain,
    ( v3_pre_topc(k1_tops_1(X0_44,X0_43),X0_44)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_763,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_167,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | m1_subset_1(k1_tops_1(X0_44,X0_43),k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_752,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_3,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_165,plain,
    ( r1_tarski(k1_tops_1(X0_44,X0_43),X0_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_733,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_174,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_163])).

cnf(c_10,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1632,c_1361,c_1251,c_948,c_831,c_828,c_772,c_763,c_752,c_733,c_174,c_10,c_11,c_12,c_13,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:55:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.79/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/0.92  
% 2.79/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/0.92  
% 2.79/0.92  ------  iProver source info
% 2.79/0.92  
% 2.79/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.79/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/0.92  git: non_committed_changes: false
% 2.79/0.92  git: last_make_outside_of_git: false
% 2.79/0.92  
% 2.79/0.92  ------ 
% 2.79/0.92  ------ Parsing...
% 2.79/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/0.92  
% 2.79/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 2.79/0.92  
% 2.79/0.92  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/0.92  
% 2.79/0.92  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/0.92  ------ Proving...
% 2.79/0.92  ------ Problem Properties 
% 2.79/0.92  
% 2.79/0.92  
% 2.79/0.92  clauses                                 20
% 2.79/0.92  conjectures                             7
% 2.79/0.92  EPR                                     7
% 2.79/0.92  Horn                                    15
% 2.79/0.92  unary                                   6
% 2.79/0.92  binary                                  3
% 2.79/0.92  lits                                    64
% 2.79/0.92  lits eq                                 2
% 2.79/0.92  fd_pure                                 0
% 2.79/0.92  fd_pseudo                               0
% 2.79/0.92  fd_cond                                 0
% 2.79/0.92  fd_pseudo_cond                          0
% 2.79/0.92  AC symbols                              0
% 2.79/0.92  
% 2.79/0.92  ------ Input Options Time Limit: Unbounded
% 2.79/0.92  
% 2.79/0.92  
% 2.79/0.92  ------ 
% 2.79/0.92  Current options:
% 2.79/0.92  ------ 
% 2.79/0.92  
% 2.79/0.92  
% 2.79/0.92  
% 2.79/0.92  
% 2.79/0.92  ------ Proving...
% 2.79/0.92  
% 2.79/0.92  
% 2.79/0.92  % SZS status Theorem for theBenchmark.p
% 2.79/0.92  
% 2.79/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/0.92  
% 2.79/0.92  fof(f1,axiom,(
% 2.79/0.92    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.92  
% 2.79/0.92  fof(f10,plain,(
% 2.79/0.92    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.79/0.92    inference(unused_predicate_definition_removal,[],[f1])).
% 2.79/0.92  
% 2.79/0.92  fof(f11,plain,(
% 2.79/0.92    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.79/0.92    inference(ennf_transformation,[],[f10])).
% 2.79/0.92  
% 2.79/0.92  fof(f30,plain,(
% 2.79/0.92    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.79/0.92    inference(cnf_transformation,[],[f11])).
% 2.79/0.92  
% 2.79/0.92  fof(f6,axiom,(
% 2.79/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.92  
% 2.79/0.92  fof(f19,plain,(
% 2.79/0.92    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.79/0.92    inference(ennf_transformation,[],[f6])).
% 2.79/0.92  
% 2.79/0.92  fof(f20,plain,(
% 2.79/0.92    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.79/0.92    inference(flattening,[],[f19])).
% 2.79/0.92  
% 2.79/0.92  fof(f25,plain,(
% 2.79/0.92    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.79/0.92    inference(nnf_transformation,[],[f20])).
% 2.79/0.92  
% 2.79/0.92  fof(f37,plain,(
% 2.79/0.92    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.79/0.92    inference(cnf_transformation,[],[f25])).
% 2.79/0.92  
% 2.79/0.92  fof(f5,axiom,(
% 2.79/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.92  
% 2.79/0.92  fof(f17,plain,(
% 2.79/0.92    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.79/0.92    inference(ennf_transformation,[],[f5])).
% 2.79/0.92  
% 2.79/0.92  fof(f18,plain,(
% 2.79/0.92    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.79/0.92    inference(flattening,[],[f17])).
% 2.79/0.92  
% 2.79/0.92  fof(f34,plain,(
% 2.79/0.92    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.79/0.92    inference(cnf_transformation,[],[f18])).
% 2.79/0.92  
% 2.79/0.92  fof(f8,conjecture,(
% 2.79/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.92  
% 2.79/0.92  fof(f9,negated_conjecture,(
% 2.79/0.92    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.79/0.92    inference(negated_conjecture,[],[f8])).
% 2.79/0.92  
% 2.79/0.92  fof(f23,plain,(
% 2.79/0.92    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.79/0.92    inference(ennf_transformation,[],[f9])).
% 2.79/0.92  
% 2.79/0.92  fof(f24,plain,(
% 2.79/0.92    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.79/0.92    inference(flattening,[],[f23])).
% 2.79/0.92  
% 2.79/0.92  fof(f28,plain,(
% 2.79/0.92    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.79/0.92    introduced(choice_axiom,[])).
% 2.79/0.92  
% 2.79/0.92  fof(f27,plain,(
% 2.79/0.92    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 2.79/0.92    introduced(choice_axiom,[])).
% 2.79/0.92  
% 2.79/0.92  fof(f26,plain,(
% 2.79/0.92    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.79/0.92    introduced(choice_axiom,[])).
% 2.79/0.92  
% 2.79/0.92  fof(f29,plain,(
% 2.79/0.92    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.79/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f28,f27,f26])).
% 2.79/0.92  
% 2.79/0.92  fof(f43,plain,(
% 2.79/0.92    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.79/0.92    inference(cnf_transformation,[],[f29])).
% 2.79/0.92  
% 2.79/0.92  fof(f45,plain,(
% 2.79/0.92    ( ! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) )),
% 2.79/0.92    inference(cnf_transformation,[],[f29])).
% 2.79/0.92  
% 2.79/0.92  fof(f36,plain,(
% 2.79/0.92    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.79/0.92    inference(cnf_transformation,[],[f25])).
% 2.79/0.92  
% 2.79/0.92  fof(f7,axiom,(
% 2.79/0.92    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.92  
% 2.79/0.92  fof(f21,plain,(
% 2.79/0.92    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.79/0.92    inference(ennf_transformation,[],[f7])).
% 2.79/0.92  
% 2.79/0.92  fof(f22,plain,(
% 2.79/0.92    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.79/0.92    inference(flattening,[],[f21])).
% 2.79/0.92  
% 2.79/0.92  fof(f38,plain,(
% 2.79/0.92    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.79/0.92    inference(cnf_transformation,[],[f22])).
% 2.79/0.92  
% 2.79/0.92  fof(f3,axiom,(
% 2.79/0.92    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.92  
% 2.79/0.92  fof(f14,plain,(
% 2.79/0.92    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.79/0.92    inference(ennf_transformation,[],[f3])).
% 2.79/0.92  
% 2.79/0.92  fof(f15,plain,(
% 2.79/0.92    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.79/0.92    inference(flattening,[],[f14])).
% 2.79/0.92  
% 2.79/0.92  fof(f32,plain,(
% 2.79/0.92    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.79/0.92    inference(cnf_transformation,[],[f15])).
% 2.79/0.92  
% 2.79/0.92  fof(f2,axiom,(
% 2.79/0.92    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.92  
% 2.79/0.92  fof(f12,plain,(
% 2.79/0.92    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.79/0.92    inference(ennf_transformation,[],[f2])).
% 2.79/0.92  
% 2.79/0.92  fof(f13,plain,(
% 2.79/0.92    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.79/0.92    inference(flattening,[],[f12])).
% 2.79/0.92  
% 2.79/0.92  fof(f31,plain,(
% 2.79/0.92    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.79/0.92    inference(cnf_transformation,[],[f13])).
% 2.79/0.92  
% 2.79/0.92  fof(f4,axiom,(
% 2.79/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.79/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/0.92  
% 2.79/0.92  fof(f16,plain,(
% 2.79/0.92    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.79/0.92    inference(ennf_transformation,[],[f4])).
% 2.79/0.92  
% 2.79/0.92  fof(f33,plain,(
% 2.79/0.92    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.79/0.92    inference(cnf_transformation,[],[f16])).
% 2.79/0.92  
% 2.79/0.92  fof(f44,plain,(
% 2.79/0.92    m1_connsp_2(sK2,sK0,sK1)),
% 2.79/0.92    inference(cnf_transformation,[],[f29])).
% 2.79/0.92  
% 2.79/0.92  fof(f42,plain,(
% 2.79/0.92    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.79/0.92    inference(cnf_transformation,[],[f29])).
% 2.79/0.92  
% 2.79/0.92  fof(f41,plain,(
% 2.79/0.92    l1_pre_topc(sK0)),
% 2.79/0.92    inference(cnf_transformation,[],[f29])).
% 2.79/0.92  
% 2.79/0.92  fof(f40,plain,(
% 2.79/0.92    v2_pre_topc(sK0)),
% 2.79/0.92    inference(cnf_transformation,[],[f29])).
% 2.79/0.92  
% 2.79/0.92  fof(f39,plain,(
% 2.79/0.92    ~v2_struct_0(sK0)),
% 2.79/0.92    inference(cnf_transformation,[],[f29])).
% 2.79/0.92  
% 2.79/0.92  cnf(c_0,plain,
% 2.79/0.92      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.79/0.92      inference(cnf_transformation,[],[f30]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_168,plain,
% 2.79/0.92      ( ~ r2_hidden(X0_43,X1_43) | ~ v1_xboole_0(X1_43) ),
% 2.79/0.92      inference(subtyping,[status(esa)],[c_0]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_1630,plain,
% 2.79/0.92      ( ~ r2_hidden(X0_43,k1_tops_1(sK0,sK2))
% 2.79/0.92      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_168]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_1632,plain,
% 2.79/0.92      ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.79/0.92      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_1630]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_6,plain,
% 2.79/0.92      ( m1_connsp_2(X0,X1,X2)
% 2.79/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.92      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.79/0.92      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.79/0.92      | v2_struct_0(X1)
% 2.79/0.92      | ~ v2_pre_topc(X1)
% 2.79/0.92      | ~ l1_pre_topc(X1) ),
% 2.79/0.92      inference(cnf_transformation,[],[f37]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_162,plain,
% 2.79/0.92      ( m1_connsp_2(X0_43,X0_44,X1_43)
% 2.79/0.92      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.92      | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
% 2.79/0.92      | ~ r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
% 2.79/0.92      | v2_struct_0(X0_44)
% 2.79/0.92      | ~ v2_pre_topc(X0_44)
% 2.79/0.92      | ~ l1_pre_topc(X0_44) ),
% 2.79/0.92      inference(subtyping,[status(esa)],[c_6]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_1361,plain,
% 2.79/0.92      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 2.79/0.92      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.92      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.79/0.92      | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 2.79/0.92      | v2_struct_0(sK0)
% 2.79/0.92      | ~ v2_pre_topc(sK0)
% 2.79/0.92      | ~ l1_pre_topc(sK0) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_162]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_178,plain,
% 2.79/0.92      ( ~ r2_hidden(X0_43,X1_43)
% 2.79/0.92      | r2_hidden(X0_43,X2_43)
% 2.79/0.92      | X2_43 != X1_43 ),
% 2.79/0.92      theory(equality) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_871,plain,
% 2.79/0.92      ( r2_hidden(sK1,X0_43)
% 2.79/0.92      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.79/0.92      | X0_43 != k1_tops_1(sK0,sK2) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_178]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_1251,plain,
% 2.79/0.92      ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 2.79/0.92      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.79/0.92      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_871]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_5,plain,
% 2.79/0.92      ( ~ v3_pre_topc(X0,X1)
% 2.79/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.79/0.92      | ~ v2_pre_topc(X3)
% 2.79/0.92      | ~ l1_pre_topc(X3)
% 2.79/0.92      | ~ l1_pre_topc(X1)
% 2.79/0.92      | k1_tops_1(X1,X0) = X0 ),
% 2.79/0.92      inference(cnf_transformation,[],[f34]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_163,plain,
% 2.79/0.92      ( ~ v3_pre_topc(X0_43,X0_44)
% 2.79/0.92      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.92      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(X1_44)))
% 2.79/0.92      | ~ v2_pre_topc(X1_44)
% 2.79/0.92      | ~ l1_pre_topc(X1_44)
% 2.79/0.92      | ~ l1_pre_topc(X0_44)
% 2.79/0.92      | k1_tops_1(X0_44,X0_43) = X0_43 ),
% 2.79/0.92      inference(subtyping,[status(esa)],[c_5]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_172,plain,
% 2.79/0.92      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.92      | ~ v2_pre_topc(X0_44)
% 2.79/0.92      | ~ l1_pre_topc(X0_44)
% 2.79/0.92      | ~ sP2_iProver_split ),
% 2.79/0.92      inference(splitting,
% 2.79/0.92                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.79/0.92                [c_163]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_11,negated_conjecture,
% 2.79/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.79/0.92      inference(cnf_transformation,[],[f43]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_158,negated_conjecture,
% 2.79/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.79/0.92      inference(subtyping,[status(esa)],[c_11]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_948,plain,
% 2.79/0.92      ( ~ v2_pre_topc(sK0) | ~ l1_pre_topc(sK0) | ~ sP2_iProver_split ),
% 2.79/0.92      inference(resolution,[status(thm)],[c_172,c_158]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_173,plain,
% 2.79/0.92      ( ~ v3_pre_topc(X0_43,X0_44)
% 2.79/0.92      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.92      | ~ l1_pre_topc(X0_44)
% 2.79/0.92      | k1_tops_1(X0_44,X0_43) = X0_43
% 2.79/0.92      | ~ sP3_iProver_split ),
% 2.79/0.92      inference(splitting,
% 2.79/0.92                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.79/0.92                [c_163]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_831,plain,
% 2.79/0.92      ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 2.79/0.92      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.92      | ~ l1_pre_topc(sK0)
% 2.79/0.92      | ~ sP3_iProver_split
% 2.79/0.92      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_173]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_9,negated_conjecture,
% 2.79/0.92      ( ~ m1_connsp_2(X0,sK0,sK1)
% 2.79/0.92      | ~ r1_tarski(X0,sK2)
% 2.79/0.92      | ~ v3_pre_topc(X0,sK0)
% 2.79/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.92      | v1_xboole_0(X0) ),
% 2.79/0.92      inference(cnf_transformation,[],[f45]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_160,negated_conjecture,
% 2.79/0.92      ( ~ m1_connsp_2(X0_43,sK0,sK1)
% 2.79/0.92      | ~ r1_tarski(X0_43,sK2)
% 2.79/0.92      | ~ v3_pre_topc(X0_43,sK0)
% 2.79/0.92      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.92      | v1_xboole_0(X0_43) ),
% 2.79/0.92      inference(subtyping,[status(esa)],[c_9]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_828,plain,
% 2.79/0.92      ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 2.79/0.92      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.79/0.92      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 2.79/0.92      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.92      | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_160]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_7,plain,
% 2.79/0.92      ( ~ m1_connsp_2(X0,X1,X2)
% 2.79/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.92      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.79/0.92      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.79/0.92      | v2_struct_0(X1)
% 2.79/0.92      | ~ v2_pre_topc(X1)
% 2.79/0.92      | ~ l1_pre_topc(X1) ),
% 2.79/0.92      inference(cnf_transformation,[],[f36]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_8,plain,
% 2.79/0.92      ( ~ m1_connsp_2(X0,X1,X2)
% 2.79/0.92      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.92      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.79/0.92      | v2_struct_0(X1)
% 2.79/0.92      | ~ v2_pre_topc(X1)
% 2.79/0.92      | ~ l1_pre_topc(X1) ),
% 2.79/0.92      inference(cnf_transformation,[],[f38]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_128,plain,
% 2.79/0.92      ( ~ m1_connsp_2(X0,X1,X2)
% 2.79/0.92      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.79/0.92      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.79/0.92      | v2_struct_0(X1)
% 2.79/0.92      | ~ v2_pre_topc(X1)
% 2.79/0.92      | ~ l1_pre_topc(X1) ),
% 2.79/0.92      inference(global_propositional_subsumption,[status(thm)],[c_7,c_8]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_153,plain,
% 2.79/0.92      ( ~ m1_connsp_2(X0_43,X0_44,X1_43)
% 2.79/0.92      | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
% 2.79/0.92      | r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
% 2.79/0.92      | v2_struct_0(X0_44)
% 2.79/0.92      | ~ v2_pre_topc(X0_44)
% 2.79/0.92      | ~ l1_pre_topc(X0_44) ),
% 2.79/0.92      inference(subtyping,[status(esa)],[c_128]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_772,plain,
% 2.79/0.92      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 2.79/0.92      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.79/0.92      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.79/0.92      | v2_struct_0(sK0)
% 2.79/0.92      | ~ v2_pre_topc(sK0)
% 2.79/0.92      | ~ l1_pre_topc(sK0) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_153]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_2,plain,
% 2.79/0.92      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.79/0.92      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.79/0.92      | ~ v2_pre_topc(X0)
% 2.79/0.92      | ~ l1_pre_topc(X0) ),
% 2.79/0.92      inference(cnf_transformation,[],[f32]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_166,plain,
% 2.79/0.92      ( v3_pre_topc(k1_tops_1(X0_44,X0_43),X0_44)
% 2.79/0.92      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.92      | ~ v2_pre_topc(X0_44)
% 2.79/0.92      | ~ l1_pre_topc(X0_44) ),
% 2.79/0.92      inference(subtyping,[status(esa)],[c_2]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_763,plain,
% 2.79/0.92      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 2.79/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.92      | ~ v2_pre_topc(sK0)
% 2.79/0.92      | ~ l1_pre_topc(sK0) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_166]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_1,plain,
% 2.79/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.92      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.92      | ~ l1_pre_topc(X1) ),
% 2.79/0.92      inference(cnf_transformation,[],[f31]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_167,plain,
% 2.79/0.92      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.92      | m1_subset_1(k1_tops_1(X0_44,X0_43),k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.92      | ~ l1_pre_topc(X0_44) ),
% 2.79/0.92      inference(subtyping,[status(esa)],[c_1]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_752,plain,
% 2.79/0.92      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.92      | ~ l1_pre_topc(sK0) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_167]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_3,plain,
% 2.79/0.92      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 2.79/0.92      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.79/0.92      | ~ l1_pre_topc(X0) ),
% 2.79/0.92      inference(cnf_transformation,[],[f33]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_165,plain,
% 2.79/0.92      ( r1_tarski(k1_tops_1(X0_44,X0_43),X0_43)
% 2.79/0.92      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.92      | ~ l1_pre_topc(X0_44) ),
% 2.79/0.92      inference(subtyping,[status(esa)],[c_3]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_733,plain,
% 2.79/0.92      ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.79/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.92      | ~ l1_pre_topc(sK0) ),
% 2.79/0.92      inference(instantiation,[status(thm)],[c_165]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_174,plain,
% 2.79/0.92      ( sP3_iProver_split | sP2_iProver_split ),
% 2.79/0.92      inference(splitting,
% 2.79/0.92                [splitting(split),new_symbols(definition,[])],
% 2.79/0.92                [c_163]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_10,negated_conjecture,
% 2.79/0.92      ( m1_connsp_2(sK2,sK0,sK1) ),
% 2.79/0.92      inference(cnf_transformation,[],[f44]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_12,negated_conjecture,
% 2.79/0.92      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 2.79/0.92      inference(cnf_transformation,[],[f42]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_13,negated_conjecture,
% 2.79/0.92      ( l1_pre_topc(sK0) ),
% 2.79/0.92      inference(cnf_transformation,[],[f41]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_14,negated_conjecture,
% 2.79/0.92      ( v2_pre_topc(sK0) ),
% 2.79/0.92      inference(cnf_transformation,[],[f40]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(c_15,negated_conjecture,
% 2.79/0.92      ( ~ v2_struct_0(sK0) ),
% 2.79/0.92      inference(cnf_transformation,[],[f39]) ).
% 2.79/0.92  
% 2.79/0.92  cnf(contradiction,plain,
% 2.79/0.92      ( $false ),
% 2.79/0.92      inference(minisat,
% 2.79/0.92                [status(thm)],
% 2.79/0.92                [c_1632,c_1361,c_1251,c_948,c_831,c_828,c_772,c_763,
% 2.79/0.92                 c_752,c_733,c_174,c_10,c_11,c_12,c_13,c_14,c_15]) ).
% 2.79/0.92  
% 2.79/0.92  
% 2.79/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/0.92  
% 2.79/0.92  ------                               Statistics
% 2.79/0.92  
% 2.79/0.92  ------ Selected
% 2.79/0.92  
% 2.79/0.92  total_time:                             0.084
% 2.79/0.92  
%------------------------------------------------------------------------------

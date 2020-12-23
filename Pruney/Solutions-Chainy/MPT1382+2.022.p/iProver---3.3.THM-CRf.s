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
% DateTime   : Thu Dec  3 12:18:19 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 145 expanded)
%              Number of clauses        :   42 (  44 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  401 (1088 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f26,plain,(
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

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,
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

fof(f30,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f29,f28,f27])).

fof(f47,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_219,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X2_43))
    | ~ v1_xboole_0(X2_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1607,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_2109,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_214,plain,
    ( m1_connsp_2(X0_43,X0_44,X1_43)
    | ~ r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
    | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | v2_struct_0(X0_44)
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1200,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_228,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | r2_hidden(X0_43,X2_43)
    | X2_43 != X1_43 ),
    theory(equality)).

cnf(c_969,plain,
    ( r2_hidden(sK1,X0_43)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | X0_43 != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_1106,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_221,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1071,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
    | m1_subset_1(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_6,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_215,plain,
    ( r1_tarski(k1_tops_1(X0_44,X0_43),X0_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_923,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_10,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ v3_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_212,negated_conjecture,
    ( ~ m1_connsp_2(X0_43,sK0,sK1)
    | ~ v3_pre_topc(X0_43,sK0)
    | ~ r1_tarski(X0_43,sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_909,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_9])).

cnf(c_182,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_205,plain,
    ( ~ m1_connsp_2(X0_43,X0_44,X1_43)
    | r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
    | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
    | v2_struct_0(X0_44)
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_182])).

cnf(c_900,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_216,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,k1_tops_1(X0_44,X0_43)) = k1_tops_1(X0_44,X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_853,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_4,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_217,plain,
    ( v3_pre_topc(k1_tops_1(X0_44,X0_43),X0_44)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_850,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | m1_subset_1(k1_tops_1(X0_44,X0_43),k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_847,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_844,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_11,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2109,c_1200,c_1106,c_1071,c_923,c_909,c_900,c_853,c_850,c_847,c_844,c_11,c_12,c_13,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:26:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.97/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/1.01  
% 2.97/1.01  ------  iProver source info
% 2.97/1.01  
% 2.97/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.97/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/1.01  git: non_committed_changes: false
% 2.97/1.01  git: last_make_outside_of_git: false
% 2.97/1.01  
% 2.97/1.01  ------ 
% 2.97/1.01  ------ Parsing...
% 2.97/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/1.01  ------ Proving...
% 2.97/1.01  ------ Problem Properties 
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  clauses                                 17
% 2.97/1.01  conjectures                             7
% 2.97/1.01  EPR                                     4
% 2.97/1.01  Horn                                    14
% 2.97/1.01  unary                                   6
% 2.97/1.01  binary                                  2
% 2.97/1.01  lits                                    50
% 2.97/1.01  lits eq                                 1
% 2.97/1.01  fd_pure                                 0
% 2.97/1.01  fd_pseudo                               0
% 2.97/1.01  fd_cond                                 0
% 2.97/1.01  fd_pseudo_cond                          0
% 2.97/1.01  AC symbols                              0
% 2.97/1.01  
% 2.97/1.01  ------ Input Options Time Limit: Unbounded
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  ------ 
% 2.97/1.01  Current options:
% 2.97/1.01  ------ 
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  ------ Proving...
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  % SZS status Theorem for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  fof(f2,axiom,(
% 2.97/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f11,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.97/1.01    inference(ennf_transformation,[],[f2])).
% 2.97/1.01  
% 2.97/1.01  fof(f33,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f11])).
% 2.97/1.01  
% 2.97/1.01  fof(f7,axiom,(
% 2.97/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f19,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.97/1.01    inference(ennf_transformation,[],[f7])).
% 2.97/1.01  
% 2.97/1.01  fof(f20,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.97/1.01    inference(flattening,[],[f19])).
% 2.97/1.01  
% 2.97/1.01  fof(f26,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.97/1.01    inference(nnf_transformation,[],[f20])).
% 2.97/1.01  
% 2.97/1.01  fof(f39,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f26])).
% 2.97/1.01  
% 2.97/1.01  fof(f1,axiom,(
% 2.97/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f25,plain,(
% 2.97/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.97/1.01    inference(nnf_transformation,[],[f1])).
% 2.97/1.01  
% 2.97/1.01  fof(f32,plain,(
% 2.97/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f25])).
% 2.97/1.01  
% 2.97/1.01  fof(f6,axiom,(
% 2.97/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f18,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.01    inference(ennf_transformation,[],[f6])).
% 2.97/1.01  
% 2.97/1.01  fof(f37,plain,(
% 2.97/1.01    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f18])).
% 2.97/1.01  
% 2.97/1.01  fof(f9,conjecture,(
% 2.97/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f10,negated_conjecture,(
% 2.97/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.97/1.01    inference(negated_conjecture,[],[f9])).
% 2.97/1.01  
% 2.97/1.01  fof(f23,plain,(
% 2.97/1.01    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.97/1.01    inference(ennf_transformation,[],[f10])).
% 2.97/1.01  
% 2.97/1.01  fof(f24,plain,(
% 2.97/1.01    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.97/1.01    inference(flattening,[],[f23])).
% 2.97/1.01  
% 2.97/1.01  fof(f29,plain,(
% 2.97/1.01    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f28,plain,(
% 2.97/1.01    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f27,plain,(
% 2.97/1.01    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f30,plain,(
% 2.97/1.01    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.97/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f29,f28,f27])).
% 2.97/1.01  
% 2.97/1.01  fof(f47,plain,(
% 2.97/1.01    ( ! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f30])).
% 2.97/1.01  
% 2.97/1.01  fof(f38,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f26])).
% 2.97/1.01  
% 2.97/1.01  fof(f8,axiom,(
% 2.97/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f21,plain,(
% 2.97/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.97/1.01    inference(ennf_transformation,[],[f8])).
% 2.97/1.01  
% 2.97/1.01  fof(f22,plain,(
% 2.97/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.97/1.01    inference(flattening,[],[f21])).
% 2.97/1.01  
% 2.97/1.01  fof(f40,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f22])).
% 2.97/1.01  
% 2.97/1.01  fof(f5,axiom,(
% 2.97/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f16,plain,(
% 2.97/1.01    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.97/1.01    inference(ennf_transformation,[],[f5])).
% 2.97/1.01  
% 2.97/1.01  fof(f17,plain,(
% 2.97/1.01    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.97/1.01    inference(flattening,[],[f16])).
% 2.97/1.01  
% 2.97/1.01  fof(f36,plain,(
% 2.97/1.01    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f17])).
% 2.97/1.01  
% 2.97/1.01  fof(f4,axiom,(
% 2.97/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f14,plain,(
% 2.97/1.01    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.97/1.01    inference(ennf_transformation,[],[f4])).
% 2.97/1.01  
% 2.97/1.01  fof(f15,plain,(
% 2.97/1.01    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.97/1.01    inference(flattening,[],[f14])).
% 2.97/1.01  
% 2.97/1.01  fof(f35,plain,(
% 2.97/1.01    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f15])).
% 2.97/1.01  
% 2.97/1.01  fof(f3,axiom,(
% 2.97/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f12,plain,(
% 2.97/1.01    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.97/1.01    inference(ennf_transformation,[],[f3])).
% 2.97/1.01  
% 2.97/1.01  fof(f13,plain,(
% 2.97/1.01    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.97/1.01    inference(flattening,[],[f12])).
% 2.97/1.01  
% 2.97/1.01  fof(f34,plain,(
% 2.97/1.01    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f13])).
% 2.97/1.01  
% 2.97/1.01  fof(f46,plain,(
% 2.97/1.01    m1_connsp_2(sK2,sK0,sK1)),
% 2.97/1.01    inference(cnf_transformation,[],[f30])).
% 2.97/1.01  
% 2.97/1.01  fof(f45,plain,(
% 2.97/1.01    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.97/1.01    inference(cnf_transformation,[],[f30])).
% 2.97/1.01  
% 2.97/1.01  fof(f44,plain,(
% 2.97/1.01    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.97/1.01    inference(cnf_transformation,[],[f30])).
% 2.97/1.01  
% 2.97/1.01  fof(f43,plain,(
% 2.97/1.01    l1_pre_topc(sK0)),
% 2.97/1.01    inference(cnf_transformation,[],[f30])).
% 2.97/1.01  
% 2.97/1.01  fof(f42,plain,(
% 2.97/1.01    v2_pre_topc(sK0)),
% 2.97/1.01    inference(cnf_transformation,[],[f30])).
% 2.97/1.01  
% 2.97/1.01  fof(f41,plain,(
% 2.97/1.01    ~v2_struct_0(sK0)),
% 2.97/1.01    inference(cnf_transformation,[],[f30])).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2,plain,
% 2.97/1.01      ( ~ r2_hidden(X0,X1)
% 2.97/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.97/1.01      | ~ v1_xboole_0(X2) ),
% 2.97/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_219,plain,
% 2.97/1.01      ( ~ r2_hidden(X0_43,X1_43)
% 2.97/1.01      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X2_43))
% 2.97/1.01      | ~ v1_xboole_0(X2_43) ),
% 2.97/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1607,plain,
% 2.97/1.01      ( ~ r2_hidden(X0_43,X1_43)
% 2.97/1.01      | ~ m1_subset_1(X1_43,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
% 2.97/1.01      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_219]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2109,plain,
% 2.97/1.01      ( ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 2.97/1.01      | ~ m1_subset_1(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
% 2.97/1.01      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_1607]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_7,plain,
% 2.97/1.01      ( m1_connsp_2(X0,X1,X2)
% 2.97/1.01      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.97/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.01      | v2_struct_0(X1)
% 2.97/1.01      | ~ v2_pre_topc(X1)
% 2.97/1.01      | ~ l1_pre_topc(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_214,plain,
% 2.97/1.01      ( m1_connsp_2(X0_43,X0_44,X1_43)
% 2.97/1.01      | ~ r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
% 2.97/1.01      | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
% 2.97/1.01      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.97/1.01      | v2_struct_0(X0_44)
% 2.97/1.01      | ~ v2_pre_topc(X0_44)
% 2.97/1.01      | ~ l1_pre_topc(X0_44) ),
% 2.97/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1200,plain,
% 2.97/1.01      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 2.97/1.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 2.97/1.01      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.97/1.01      | v2_struct_0(sK0)
% 2.97/1.01      | ~ v2_pre_topc(sK0)
% 2.97/1.01      | ~ l1_pre_topc(sK0) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_214]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_228,plain,
% 2.97/1.01      ( ~ r2_hidden(X0_43,X1_43)
% 2.97/1.01      | r2_hidden(X0_43,X2_43)
% 2.97/1.01      | X2_43 != X1_43 ),
% 2.97/1.01      theory(equality) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_969,plain,
% 2.97/1.01      ( r2_hidden(sK1,X0_43)
% 2.97/1.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.97/1.01      | X0_43 != k1_tops_1(sK0,sK2) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_228]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1106,plain,
% 2.97/1.01      ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 2.97/1.01      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.97/1.01      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_969]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_0,plain,
% 2.97/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_221,plain,
% 2.97/1.01      ( ~ r1_tarski(X0_43,X1_43)
% 2.97/1.01      | m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) ),
% 2.97/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1071,plain,
% 2.97/1.01      ( ~ r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
% 2.97/1.01      | m1_subset_1(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_221]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_6,plain,
% 2.97/1.01      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 2.97/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.97/1.01      | ~ l1_pre_topc(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_215,plain,
% 2.97/1.01      ( r1_tarski(k1_tops_1(X0_44,X0_43),X0_43)
% 2.97/1.01      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.97/1.01      | ~ l1_pre_topc(X0_44) ),
% 2.97/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_923,plain,
% 2.97/1.01      ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
% 2.97/1.01      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | ~ l1_pre_topc(sK0) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_215]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_10,negated_conjecture,
% 2.97/1.01      ( ~ m1_connsp_2(X0,sK0,sK1)
% 2.97/1.01      | ~ v3_pre_topc(X0,sK0)
% 2.97/1.01      | ~ r1_tarski(X0,sK2)
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | v1_xboole_0(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_212,negated_conjecture,
% 2.97/1.01      ( ~ m1_connsp_2(X0_43,sK0,sK1)
% 2.97/1.01      | ~ v3_pre_topc(X0_43,sK0)
% 2.97/1.01      | ~ r1_tarski(X0_43,sK2)
% 2.97/1.01      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | v1_xboole_0(X0_43) ),
% 2.97/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_909,plain,
% 2.97/1.01      ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 2.97/1.01      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 2.97/1.01      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.97/1.01      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_212]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_8,plain,
% 2.97/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.97/1.01      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.97/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.01      | v2_struct_0(X1)
% 2.97/1.01      | ~ v2_pre_topc(X1)
% 2.97/1.01      | ~ l1_pre_topc(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_9,plain,
% 2.97/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.97/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.01      | v2_struct_0(X1)
% 2.97/1.01      | ~ v2_pre_topc(X1)
% 2.97/1.01      | ~ l1_pre_topc(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_181,plain,
% 2.97/1.01      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.01      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.97/1.01      | ~ m1_connsp_2(X0,X1,X2)
% 2.97/1.01      | v2_struct_0(X1)
% 2.97/1.01      | ~ v2_pre_topc(X1)
% 2.97/1.01      | ~ l1_pre_topc(X1) ),
% 2.97/1.01      inference(global_propositional_subsumption,[status(thm)],[c_8,c_9]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_182,plain,
% 2.97/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 2.97/1.01      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.97/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.01      | v2_struct_0(X1)
% 2.97/1.01      | ~ v2_pre_topc(X1)
% 2.97/1.01      | ~ l1_pre_topc(X1) ),
% 2.97/1.01      inference(renaming,[status(thm)],[c_181]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_205,plain,
% 2.97/1.01      ( ~ m1_connsp_2(X0_43,X0_44,X1_43)
% 2.97/1.01      | r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
% 2.97/1.01      | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
% 2.97/1.01      | v2_struct_0(X0_44)
% 2.97/1.01      | ~ v2_pre_topc(X0_44)
% 2.97/1.01      | ~ l1_pre_topc(X0_44) ),
% 2.97/1.01      inference(subtyping,[status(esa)],[c_182]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_900,plain,
% 2.97/1.01      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 2.97/1.01      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.97/1.01      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.97/1.01      | v2_struct_0(sK0)
% 2.97/1.01      | ~ v2_pre_topc(sK0)
% 2.97/1.01      | ~ l1_pre_topc(sK0) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_205]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.01      | ~ l1_pre_topc(X1)
% 2.97/1.01      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_216,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.97/1.01      | ~ l1_pre_topc(X0_44)
% 2.97/1.01      | k1_tops_1(X0_44,k1_tops_1(X0_44,X0_43)) = k1_tops_1(X0_44,X0_43) ),
% 2.97/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_853,plain,
% 2.97/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | ~ l1_pre_topc(sK0)
% 2.97/1.01      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_216]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4,plain,
% 2.97/1.01      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.97/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.97/1.01      | ~ v2_pre_topc(X0)
% 2.97/1.01      | ~ l1_pre_topc(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_217,plain,
% 2.97/1.01      ( v3_pre_topc(k1_tops_1(X0_44,X0_43),X0_44)
% 2.97/1.01      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.97/1.01      | ~ v2_pre_topc(X0_44)
% 2.97/1.01      | ~ l1_pre_topc(X0_44) ),
% 2.97/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_850,plain,
% 2.97/1.01      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 2.97/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | ~ v2_pre_topc(sK0)
% 2.97/1.01      | ~ l1_pre_topc(sK0) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_217]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.01      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.01      | ~ l1_pre_topc(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_218,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.97/1.01      | m1_subset_1(k1_tops_1(X0_44,X0_43),k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.97/1.01      | ~ l1_pre_topc(X0_44) ),
% 2.97/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_847,plain,
% 2.97/1.01      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | ~ l1_pre_topc(sK0) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_218]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_844,plain,
% 2.97/1.01      ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.97/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.01      | ~ l1_pre_topc(sK0) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_215]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_11,negated_conjecture,
% 2.97/1.01      ( m1_connsp_2(sK2,sK0,sK1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_12,negated_conjecture,
% 2.97/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.97/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_13,negated_conjecture,
% 2.97/1.01      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_14,negated_conjecture,
% 2.97/1.01      ( l1_pre_topc(sK0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_15,negated_conjecture,
% 2.97/1.01      ( v2_pre_topc(sK0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_16,negated_conjecture,
% 2.97/1.01      ( ~ v2_struct_0(sK0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(contradiction,plain,
% 2.97/1.01      ( $false ),
% 2.97/1.01      inference(minisat,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_2109,c_1200,c_1106,c_1071,c_923,c_909,c_900,c_853,
% 2.97/1.01                 c_850,c_847,c_844,c_11,c_12,c_13,c_14,c_15,c_16]) ).
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  ------                               Statistics
% 2.97/1.01  
% 2.97/1.01  ------ Selected
% 2.97/1.01  
% 2.97/1.01  total_time:                             0.064
% 2.97/1.01  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:17 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 147 expanded)
%              Number of clauses        :   45 (  45 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  404 (1082 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30,f29,f28])).

fof(f48,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | ~ v1_xboole_0(X1_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1239,plain,
    ( ~ r2_hidden(X0_43,k1_tops_1(sK0,sK2))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_1241,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1239])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_213,plain,
    ( m1_connsp_2(X0_43,X0_44,X1_43)
    | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
    | v2_struct_0(X0_44)
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1168,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | r2_hidden(X0_43,X2_43)
    | X2_43 != X1_43 ),
    theory(equality)).

cnf(c_959,plain,
    ( r2_hidden(sK1,X0_43)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | X0_43 != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_1064,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_959])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_218,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1048,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_219,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X0_43)
    | r1_tarski(X2_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_921,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0_43)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,X0_43) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_1028,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_10,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_211,negated_conjecture,
    ( ~ m1_connsp_2(X0_43,sK0,sK1)
    | ~ v3_pre_topc(X0_43,sK0)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_43,sK2)
    | v1_xboole_0(X0_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_910,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_9])).

cnf(c_181,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_180])).

cnf(c_204,plain,
    ( ~ m1_connsp_2(X0_43,X0_44,X1_43)
    | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
    | r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
    | v2_struct_0(X0_44)
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_181])).

cnf(c_896,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,k1_tops_1(X0_44,X0_43)) = k1_tops_1(X0_44,X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_847,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_4,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_216,plain,
    ( v3_pre_topc(k1_tops_1(X0_44,X0_43),X0_44)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_844,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | r1_tarski(k1_tops_1(X0_44,X0_43),X0_43)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_841,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_822,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_11,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1241,c_1168,c_1064,c_1048,c_1028,c_910,c_896,c_847,c_844,c_841,c_822,c_11,c_12,c_13,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:11:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.79/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/0.98  
% 2.79/0.98  ------  iProver source info
% 2.79/0.98  
% 2.79/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.79/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/0.98  git: non_committed_changes: false
% 2.79/0.98  git: last_make_outside_of_git: false
% 2.79/0.98  
% 2.79/0.98  ------ 
% 2.79/0.98  ------ Parsing...
% 2.79/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/0.98  ------ Proving...
% 2.79/0.98  ------ Problem Properties 
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  clauses                                 17
% 2.79/0.98  conjectures                             7
% 2.79/0.98  EPR                                     6
% 2.79/0.98  Horn                                    14
% 2.79/0.98  unary                                   6
% 2.79/0.98  binary                                  3
% 2.79/0.98  lits                                    49
% 2.79/0.98  lits eq                                 1
% 2.79/0.98  fd_pure                                 0
% 2.79/0.98  fd_pseudo                               0
% 2.79/0.98  fd_cond                                 0
% 2.79/0.98  fd_pseudo_cond                          0
% 2.79/0.98  AC symbols                              0
% 2.79/0.98  
% 2.79/0.98  ------ Input Options Time Limit: Unbounded
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  ------ 
% 2.79/0.98  Current options:
% 2.79/0.98  ------ 
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  ------ Proving...
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  % SZS status Theorem for theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  fof(f1,axiom,(
% 2.79/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f11,plain,(
% 2.79/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.79/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 2.79/0.98  
% 2.79/0.98  fof(f12,plain,(
% 2.79/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.79/0.98    inference(ennf_transformation,[],[f11])).
% 2.79/0.98  
% 2.79/0.98  fof(f32,plain,(
% 2.79/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f12])).
% 2.79/0.98  
% 2.79/0.98  fof(f7,axiom,(
% 2.79/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f20,plain,(
% 2.79/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.79/0.98    inference(ennf_transformation,[],[f7])).
% 2.79/0.98  
% 2.79/0.98  fof(f21,plain,(
% 2.79/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.79/0.98    inference(flattening,[],[f20])).
% 2.79/0.98  
% 2.79/0.98  fof(f27,plain,(
% 2.79/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.79/0.98    inference(nnf_transformation,[],[f21])).
% 2.79/0.98  
% 2.79/0.98  fof(f40,plain,(
% 2.79/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f27])).
% 2.79/0.98  
% 2.79/0.98  fof(f3,axiom,(
% 2.79/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.98  
% 2.79/0.98  fof(f26,plain,(
% 2.79/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.79/0.98    inference(nnf_transformation,[],[f3])).
% 2.79/0.98  
% 2.79/0.98  fof(f35,plain,(
% 2.79/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.79/0.98    inference(cnf_transformation,[],[f26])).
% 2.79/0.98  
% 2.79/0.98  fof(f2,axiom,(
% 2.79/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.79/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f13,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.79/0.99    inference(ennf_transformation,[],[f2])).
% 2.79/0.99  
% 2.79/0.99  fof(f14,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.79/0.99    inference(flattening,[],[f13])).
% 2.79/0.99  
% 2.79/0.99  fof(f33,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f14])).
% 2.79/0.99  
% 2.79/0.99  fof(f9,conjecture,(
% 2.79/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f10,negated_conjecture,(
% 2.79/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.79/0.99    inference(negated_conjecture,[],[f9])).
% 2.79/0.99  
% 2.79/0.99  fof(f24,plain,(
% 2.79/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.79/0.99    inference(ennf_transformation,[],[f10])).
% 2.79/0.99  
% 2.79/0.99  fof(f25,plain,(
% 2.79/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.79/0.99    inference(flattening,[],[f24])).
% 2.79/0.99  
% 2.79/0.99  fof(f30,plain,(
% 2.79/0.99    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f29,plain,(
% 2.79/0.99    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f28,plain,(
% 2.79/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f31,plain,(
% 2.79/0.99    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30,f29,f28])).
% 2.79/0.99  
% 2.79/0.99  fof(f48,plain,(
% 2.79/0.99    ( ! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f31])).
% 2.79/0.99  
% 2.79/0.99  fof(f39,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f27])).
% 2.79/0.99  
% 2.79/0.99  fof(f8,axiom,(
% 2.79/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f22,plain,(
% 2.79/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.79/0.99    inference(ennf_transformation,[],[f8])).
% 2.79/0.99  
% 2.79/0.99  fof(f23,plain,(
% 2.79/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.79/0.99    inference(flattening,[],[f22])).
% 2.79/0.99  
% 2.79/0.99  fof(f41,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f23])).
% 2.79/0.99  
% 2.79/0.99  fof(f5,axiom,(
% 2.79/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f17,plain,(
% 2.79/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.79/0.99    inference(ennf_transformation,[],[f5])).
% 2.79/0.99  
% 2.79/0.99  fof(f18,plain,(
% 2.79/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.79/0.99    inference(flattening,[],[f17])).
% 2.79/0.99  
% 2.79/0.99  fof(f37,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f18])).
% 2.79/0.99  
% 2.79/0.99  fof(f4,axiom,(
% 2.79/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f15,plain,(
% 2.79/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.79/0.99    inference(ennf_transformation,[],[f4])).
% 2.79/0.99  
% 2.79/0.99  fof(f16,plain,(
% 2.79/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.79/0.99    inference(flattening,[],[f15])).
% 2.79/0.99  
% 2.79/0.99  fof(f36,plain,(
% 2.79/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f16])).
% 2.79/0.99  
% 2.79/0.99  fof(f6,axiom,(
% 2.79/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f19,plain,(
% 2.79/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.79/0.99    inference(ennf_transformation,[],[f6])).
% 2.79/0.99  
% 2.79/0.99  fof(f38,plain,(
% 2.79/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f19])).
% 2.79/0.99  
% 2.79/0.99  fof(f34,plain,(
% 2.79/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f26])).
% 2.79/0.99  
% 2.79/0.99  fof(f47,plain,(
% 2.79/0.99    m1_connsp_2(sK2,sK0,sK1)),
% 2.79/0.99    inference(cnf_transformation,[],[f31])).
% 2.79/0.99  
% 2.79/0.99  fof(f46,plain,(
% 2.79/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.79/0.99    inference(cnf_transformation,[],[f31])).
% 2.79/0.99  
% 2.79/0.99  fof(f45,plain,(
% 2.79/0.99    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.79/0.99    inference(cnf_transformation,[],[f31])).
% 2.79/0.99  
% 2.79/0.99  fof(f44,plain,(
% 2.79/0.99    l1_pre_topc(sK0)),
% 2.79/0.99    inference(cnf_transformation,[],[f31])).
% 2.79/0.99  
% 2.79/0.99  fof(f43,plain,(
% 2.79/0.99    v2_pre_topc(sK0)),
% 2.79/0.99    inference(cnf_transformation,[],[f31])).
% 2.79/0.99  
% 2.79/0.99  fof(f42,plain,(
% 2.79/0.99    ~v2_struct_0(sK0)),
% 2.79/0.99    inference(cnf_transformation,[],[f31])).
% 2.79/0.99  
% 2.79/0.99  cnf(c_0,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_220,plain,
% 2.79/0.99      ( ~ r2_hidden(X0_43,X1_43) | ~ v1_xboole_0(X1_43) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1239,plain,
% 2.79/0.99      ( ~ r2_hidden(X0_43,k1_tops_1(sK0,sK2))
% 2.79/0.99      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_220]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1241,plain,
% 2.79/0.99      ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.79/0.99      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_1239]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_7,plain,
% 2.79/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.79/0.99      | v2_struct_0(X1)
% 2.79/0.99      | ~ v2_pre_topc(X1)
% 2.79/0.99      | ~ l1_pre_topc(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_213,plain,
% 2.79/0.99      ( m1_connsp_2(X0_43,X0_44,X1_43)
% 2.79/0.99      | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
% 2.79/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.99      | ~ r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
% 2.79/0.99      | v2_struct_0(X0_44)
% 2.79/0.99      | ~ v2_pre_topc(X0_44)
% 2.79/0.99      | ~ l1_pre_topc(X0_44) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1168,plain,
% 2.79/0.99      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 2.79/0.99      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.79/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 2.79/0.99      | v2_struct_0(sK0)
% 2.79/0.99      | ~ v2_pre_topc(sK0)
% 2.79/0.99      | ~ l1_pre_topc(sK0) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_213]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_224,plain,
% 2.79/0.99      ( ~ r2_hidden(X0_43,X1_43)
% 2.79/0.99      | r2_hidden(X0_43,X2_43)
% 2.79/0.99      | X2_43 != X1_43 ),
% 2.79/0.99      theory(equality) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_959,plain,
% 2.79/0.99      ( r2_hidden(sK1,X0_43)
% 2.79/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.79/0.99      | X0_43 != k1_tops_1(sK0,sK2) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_224]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1064,plain,
% 2.79/0.99      ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 2.79/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.79/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_959]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2,plain,
% 2.79/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_218,plain,
% 2.79/0.99      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 2.79/0.99      | ~ r1_tarski(X0_43,X1_43) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1048,plain,
% 2.79/0.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_218]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1,plain,
% 2.79/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_219,plain,
% 2.79/0.99      ( ~ r1_tarski(X0_43,X1_43)
% 2.79/0.99      | ~ r1_tarski(X2_43,X0_43)
% 2.79/0.99      | r1_tarski(X2_43,X1_43) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_921,plain,
% 2.79/0.99      ( r1_tarski(k1_tops_1(sK0,sK2),X0_43)
% 2.79/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.79/0.99      | ~ r1_tarski(sK2,X0_43) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_219]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1028,plain,
% 2.79/0.99      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 2.79/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.79/0.99      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_921]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_10,negated_conjecture,
% 2.79/0.99      ( ~ m1_connsp_2(X0,sK0,sK1)
% 2.79/0.99      | ~ v3_pre_topc(X0,sK0)
% 2.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.99      | ~ r1_tarski(X0,sK2)
% 2.79/0.99      | v1_xboole_0(X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_211,negated_conjecture,
% 2.79/0.99      ( ~ m1_connsp_2(X0_43,sK0,sK1)
% 2.79/0.99      | ~ v3_pre_topc(X0_43,sK0)
% 2.79/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.99      | ~ r1_tarski(X0_43,sK2)
% 2.79/0.99      | v1_xboole_0(X0_43) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_910,plain,
% 2.79/0.99      ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 2.79/0.99      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 2.79/0.99      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.79/0.99      | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_211]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_8,plain,
% 2.79/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.79/0.99      | v2_struct_0(X1)
% 2.79/0.99      | ~ v2_pre_topc(X1)
% 2.79/0.99      | ~ l1_pre_topc(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_9,plain,
% 2.79/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.79/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.99      | v2_struct_0(X1)
% 2.79/0.99      | ~ v2_pre_topc(X1)
% 2.79/0.99      | ~ l1_pre_topc(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_180,plain,
% 2.79/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.79/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 2.79/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.79/0.99      | v2_struct_0(X1)
% 2.79/0.99      | ~ v2_pre_topc(X1)
% 2.79/0.99      | ~ l1_pre_topc(X1) ),
% 2.79/0.99      inference(global_propositional_subsumption,[status(thm)],[c_8,c_9]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_181,plain,
% 2.79/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.79/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.79/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.79/0.99      | v2_struct_0(X1)
% 2.79/0.99      | ~ v2_pre_topc(X1)
% 2.79/0.99      | ~ l1_pre_topc(X1) ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_180]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_204,plain,
% 2.79/0.99      ( ~ m1_connsp_2(X0_43,X0_44,X1_43)
% 2.79/0.99      | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
% 2.79/0.99      | r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
% 2.79/0.99      | v2_struct_0(X0_44)
% 2.79/0.99      | ~ v2_pre_topc(X0_44)
% 2.79/0.99      | ~ l1_pre_topc(X0_44) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_181]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_896,plain,
% 2.79/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 2.79/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.79/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.79/0.99      | v2_struct_0(sK0)
% 2.79/0.99      | ~ v2_pre_topc(sK0)
% 2.79/0.99      | ~ l1_pre_topc(sK0) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_204]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.99      | ~ l1_pre_topc(X1)
% 2.79/0.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_215,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.99      | ~ l1_pre_topc(X0_44)
% 2.79/0.99      | k1_tops_1(X0_44,k1_tops_1(X0_44,X0_43)) = k1_tops_1(X0_44,X0_43) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_847,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.99      | ~ l1_pre_topc(sK0)
% 2.79/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_215]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4,plain,
% 2.79/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.79/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.79/0.99      | ~ v2_pre_topc(X0)
% 2.79/0.99      | ~ l1_pre_topc(X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_216,plain,
% 2.79/0.99      ( v3_pre_topc(k1_tops_1(X0_44,X0_43),X0_44)
% 2.79/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.99      | ~ v2_pre_topc(X0_44)
% 2.79/0.99      | ~ l1_pre_topc(X0_44) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_844,plain,
% 2.79/0.99      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 2.79/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.99      | ~ v2_pre_topc(sK0)
% 2.79/0.99      | ~ l1_pre_topc(sK0) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_216]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_6,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.79/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.79/0.99      | ~ l1_pre_topc(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_214,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 2.79/0.99      | r1_tarski(k1_tops_1(X0_44,X0_43),X0_43)
% 2.79/0.99      | ~ l1_pre_topc(X0_44) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_841,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.79/0.99      | ~ l1_pre_topc(sK0) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_214]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_217,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 2.79/0.99      | r1_tarski(X0_43,X1_43) ),
% 2.79/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_822,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.79/0.99      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_217]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_11,negated_conjecture,
% 2.79/0.99      ( m1_connsp_2(sK2,sK0,sK1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_12,negated_conjecture,
% 2.79/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_13,negated_conjecture,
% 2.79/0.99      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 2.79/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_14,negated_conjecture,
% 2.79/0.99      ( l1_pre_topc(sK0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_15,negated_conjecture,
% 2.79/0.99      ( v2_pre_topc(sK0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_16,negated_conjecture,
% 2.79/0.99      ( ~ v2_struct_0(sK0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(contradiction,plain,
% 2.79/0.99      ( $false ),
% 2.79/0.99      inference(minisat,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_1241,c_1168,c_1064,c_1048,c_1028,c_910,c_896,c_847,
% 2.79/0.99                 c_844,c_841,c_822,c_11,c_12,c_13,c_14,c_15,c_16]) ).
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  ------                               Statistics
% 2.79/0.99  
% 2.79/0.99  ------ Selected
% 2.79/0.99  
% 2.79/0.99  total_time:                             0.048
% 2.79/0.99  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:12 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 442 expanded)
%              Number of clauses        :   65 ( 114 expanded)
%              Number of leaves         :   12 ( 152 expanded)
%              Depth                    :   22
%              Number of atoms          :  401 (3129 expanded)
%              Number of equality atoms :   70 ( 105 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
          & m1_connsp_2(X3,X0,X1)
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1)
        & m1_connsp_2(sK4,X0,X1)
        & m1_connsp_2(X2,X0,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
              & m1_connsp_2(X3,X0,X1)
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1)
            & m1_connsp_2(X3,X0,X1)
            & m1_connsp_2(sK3,X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2)
                & m1_connsp_2(X3,X0,sK2)
                & m1_connsp_2(X2,X0,sK2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    & m1_connsp_2(X3,X0,X1)
                    & m1_connsp_2(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1)
                  & m1_connsp_2(X3,sK1,X1)
                  & m1_connsp_2(X2,sK1,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    & m1_connsp_2(sK4,sK1,sK2)
    & m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f28,f27,f26,f25])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_448,plain,
    ( r1_tarski(X0_45,k2_xboole_0(X0_45,X1_45)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_700,plain,
    ( r1_tarski(X0_45,k2_xboole_0(X0_45,X1_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_444,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_704,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_445,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_703,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X0_46))
    | k4_subset_1(X0_46,X1_45,X0_45) = k2_xboole_0(X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_702,plain,
    ( k4_subset_1(X0_46,X0_45,X1_45) = k2_xboole_0(X0_45,X1_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(X0_46)) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(X0_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_1586,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0_45,sK4) = k2_xboole_0(X0_45,sK4)
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_702])).

cnf(c_2014,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_704,c_1586])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X0_46))
    | m1_subset_1(k4_subset_1(X0_46,X1_45,X0_45),k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_701,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46)) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(X0_46)) != iProver_top
    | m1_subset_1(k4_subset_1(X0_46,X0_45,X1_45),k1_zfmisc_1(X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1_45,X0_45)
    | r1_tarski(k1_tops_1(sK1,X1_45),k1_tops_1(sK1,X0_45)) ),
    inference(subtyping,[status(esa)],[c_252])).

cnf(c_706,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1_45,X0_45) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X1_45),k1_tops_1(sK1,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_11,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_193,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_194,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_198,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_194,c_17,c_15])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_198])).

cnf(c_321,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_323,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_14,c_13])).

cnf(c_439,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(subtyping,[status(esa)],[c_323])).

cnf(c_709,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_449,plain,
    ( ~ r2_hidden(X0_45,X1_45)
    | r2_hidden(X0_45,X2_45)
    | ~ r1_tarski(X1_45,X2_45) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_699,plain,
    ( r2_hidden(X0_45,X1_45) != iProver_top
    | r2_hidden(X0_45,X2_45) = iProver_top
    | r1_tarski(X1_45,X2_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_1270,plain,
    ( r2_hidden(sK2,X0_45) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),X0_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_699])).

cnf(c_1346,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,X0_45)) = iProver_top
    | r1_tarski(sK3,X0_45) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_1270])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1420,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,X0_45)) = iProver_top
    | r1_tarski(sK3,X0_45) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1346,c_22])).

cnf(c_1428,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0_45,X1_45))) = iProver_top
    | r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),X0_45,X1_45)) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_1420])).

cnf(c_2596,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = iProver_top
    | r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2014,c_1428])).

cnf(c_2604,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = iProver_top
    | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2596,c_2014])).

cnf(c_23,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_217,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_218,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_222,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_17,c_15])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_222])).

cnf(c_296,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_298,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_14])).

cnf(c_441,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_298])).

cnf(c_707,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_297,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_730,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_731,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_957,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_21,c_22,c_23,c_297,c_731])).

cnf(c_2129,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2014,c_957])).

cnf(c_11121,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_22,c_23,c_2129])).

cnf(c_11125,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_700,c_11121])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 3.78/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.01  
% 3.78/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/1.01  
% 3.78/1.01  ------  iProver source info
% 3.78/1.01  
% 3.78/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.78/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/1.01  git: non_committed_changes: false
% 3.78/1.01  git: last_make_outside_of_git: false
% 3.78/1.01  
% 3.78/1.01  ------ 
% 3.78/1.01  
% 3.78/1.01  ------ Input Options
% 3.78/1.01  
% 3.78/1.01  --out_options                           all
% 3.78/1.01  --tptp_safe_out                         true
% 3.78/1.01  --problem_path                          ""
% 3.78/1.01  --include_path                          ""
% 3.78/1.01  --clausifier                            res/vclausify_rel
% 3.78/1.01  --clausifier_options                    ""
% 3.78/1.01  --stdin                                 false
% 3.78/1.01  --stats_out                             all
% 3.78/1.01  
% 3.78/1.01  ------ General Options
% 3.78/1.01  
% 3.78/1.01  --fof                                   false
% 3.78/1.01  --time_out_real                         305.
% 3.78/1.01  --time_out_virtual                      -1.
% 3.78/1.01  --symbol_type_check                     false
% 3.78/1.01  --clausify_out                          false
% 3.78/1.01  --sig_cnt_out                           false
% 3.78/1.01  --trig_cnt_out                          false
% 3.78/1.01  --trig_cnt_out_tolerance                1.
% 3.78/1.01  --trig_cnt_out_sk_spl                   false
% 3.78/1.01  --abstr_cl_out                          false
% 3.78/1.01  
% 3.78/1.01  ------ Global Options
% 3.78/1.01  
% 3.78/1.01  --schedule                              default
% 3.78/1.01  --add_important_lit                     false
% 3.78/1.01  --prop_solver_per_cl                    1000
% 3.78/1.01  --min_unsat_core                        false
% 3.78/1.01  --soft_assumptions                      false
% 3.78/1.01  --soft_lemma_size                       3
% 3.78/1.01  --prop_impl_unit_size                   0
% 3.78/1.01  --prop_impl_unit                        []
% 3.78/1.01  --share_sel_clauses                     true
% 3.78/1.01  --reset_solvers                         false
% 3.78/1.01  --bc_imp_inh                            [conj_cone]
% 3.78/1.01  --conj_cone_tolerance                   3.
% 3.78/1.01  --extra_neg_conj                        none
% 3.78/1.01  --large_theory_mode                     true
% 3.78/1.01  --prolific_symb_bound                   200
% 3.78/1.01  --lt_threshold                          2000
% 3.78/1.01  --clause_weak_htbl                      true
% 3.78/1.01  --gc_record_bc_elim                     false
% 3.78/1.01  
% 3.78/1.01  ------ Preprocessing Options
% 3.78/1.01  
% 3.78/1.01  --preprocessing_flag                    true
% 3.78/1.01  --time_out_prep_mult                    0.1
% 3.78/1.01  --splitting_mode                        input
% 3.78/1.01  --splitting_grd                         true
% 3.78/1.01  --splitting_cvd                         false
% 3.78/1.01  --splitting_cvd_svl                     false
% 3.78/1.01  --splitting_nvd                         32
% 3.78/1.01  --sub_typing                            true
% 3.78/1.01  --prep_gs_sim                           true
% 3.78/1.01  --prep_unflatten                        true
% 3.78/1.01  --prep_res_sim                          true
% 3.78/1.01  --prep_upred                            true
% 3.78/1.01  --prep_sem_filter                       exhaustive
% 3.78/1.01  --prep_sem_filter_out                   false
% 3.78/1.01  --pred_elim                             true
% 3.78/1.01  --res_sim_input                         true
% 3.78/1.01  --eq_ax_congr_red                       true
% 3.78/1.01  --pure_diseq_elim                       true
% 3.78/1.01  --brand_transform                       false
% 3.78/1.01  --non_eq_to_eq                          false
% 3.78/1.01  --prep_def_merge                        true
% 3.78/1.01  --prep_def_merge_prop_impl              false
% 3.78/1.01  --prep_def_merge_mbd                    true
% 3.78/1.01  --prep_def_merge_tr_red                 false
% 3.78/1.01  --prep_def_merge_tr_cl                  false
% 3.78/1.01  --smt_preprocessing                     true
% 3.78/1.01  --smt_ac_axioms                         fast
% 3.78/1.01  --preprocessed_out                      false
% 3.78/1.01  --preprocessed_stats                    false
% 3.78/1.01  
% 3.78/1.01  ------ Abstraction refinement Options
% 3.78/1.01  
% 3.78/1.01  --abstr_ref                             []
% 3.78/1.01  --abstr_ref_prep                        false
% 3.78/1.01  --abstr_ref_until_sat                   false
% 3.78/1.01  --abstr_ref_sig_restrict                funpre
% 3.78/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/1.01  --abstr_ref_under                       []
% 3.78/1.01  
% 3.78/1.01  ------ SAT Options
% 3.78/1.01  
% 3.78/1.01  --sat_mode                              false
% 3.78/1.01  --sat_fm_restart_options                ""
% 3.78/1.01  --sat_gr_def                            false
% 3.78/1.01  --sat_epr_types                         true
% 3.78/1.01  --sat_non_cyclic_types                  false
% 3.78/1.01  --sat_finite_models                     false
% 3.78/1.01  --sat_fm_lemmas                         false
% 3.78/1.01  --sat_fm_prep                           false
% 3.78/1.01  --sat_fm_uc_incr                        true
% 3.78/1.01  --sat_out_model                         small
% 3.78/1.01  --sat_out_clauses                       false
% 3.78/1.01  
% 3.78/1.01  ------ QBF Options
% 3.78/1.01  
% 3.78/1.01  --qbf_mode                              false
% 3.78/1.01  --qbf_elim_univ                         false
% 3.78/1.01  --qbf_dom_inst                          none
% 3.78/1.01  --qbf_dom_pre_inst                      false
% 3.78/1.01  --qbf_sk_in                             false
% 3.78/1.01  --qbf_pred_elim                         true
% 3.78/1.01  --qbf_split                             512
% 3.78/1.01  
% 3.78/1.01  ------ BMC1 Options
% 3.78/1.01  
% 3.78/1.01  --bmc1_incremental                      false
% 3.78/1.01  --bmc1_axioms                           reachable_all
% 3.78/1.01  --bmc1_min_bound                        0
% 3.78/1.01  --bmc1_max_bound                        -1
% 3.78/1.01  --bmc1_max_bound_default                -1
% 3.78/1.01  --bmc1_symbol_reachability              true
% 3.78/1.01  --bmc1_property_lemmas                  false
% 3.78/1.01  --bmc1_k_induction                      false
% 3.78/1.01  --bmc1_non_equiv_states                 false
% 3.78/1.01  --bmc1_deadlock                         false
% 3.78/1.01  --bmc1_ucm                              false
% 3.78/1.01  --bmc1_add_unsat_core                   none
% 3.78/1.01  --bmc1_unsat_core_children              false
% 3.78/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/1.01  --bmc1_out_stat                         full
% 3.78/1.01  --bmc1_ground_init                      false
% 3.78/1.01  --bmc1_pre_inst_next_state              false
% 3.78/1.01  --bmc1_pre_inst_state                   false
% 3.78/1.01  --bmc1_pre_inst_reach_state             false
% 3.78/1.01  --bmc1_out_unsat_core                   false
% 3.78/1.01  --bmc1_aig_witness_out                  false
% 3.78/1.01  --bmc1_verbose                          false
% 3.78/1.01  --bmc1_dump_clauses_tptp                false
% 3.78/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.78/1.01  --bmc1_dump_file                        -
% 3.78/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.78/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.78/1.01  --bmc1_ucm_extend_mode                  1
% 3.78/1.01  --bmc1_ucm_init_mode                    2
% 3.78/1.01  --bmc1_ucm_cone_mode                    none
% 3.78/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.78/1.01  --bmc1_ucm_relax_model                  4
% 3.78/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.78/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/1.01  --bmc1_ucm_layered_model                none
% 3.78/1.01  --bmc1_ucm_max_lemma_size               10
% 3.78/1.01  
% 3.78/1.01  ------ AIG Options
% 3.78/1.01  
% 3.78/1.01  --aig_mode                              false
% 3.78/1.01  
% 3.78/1.01  ------ Instantiation Options
% 3.78/1.01  
% 3.78/1.01  --instantiation_flag                    true
% 3.78/1.01  --inst_sos_flag                         true
% 3.78/1.01  --inst_sos_phase                        true
% 3.78/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/1.01  --inst_lit_sel_side                     num_symb
% 3.78/1.01  --inst_solver_per_active                1400
% 3.78/1.01  --inst_solver_calls_frac                1.
% 3.78/1.01  --inst_passive_queue_type               priority_queues
% 3.78/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/1.01  --inst_passive_queues_freq              [25;2]
% 3.78/1.01  --inst_dismatching                      true
% 3.78/1.01  --inst_eager_unprocessed_to_passive     true
% 3.78/1.01  --inst_prop_sim_given                   true
% 3.78/1.01  --inst_prop_sim_new                     false
% 3.78/1.01  --inst_subs_new                         false
% 3.78/1.01  --inst_eq_res_simp                      false
% 3.78/1.01  --inst_subs_given                       false
% 3.78/1.01  --inst_orphan_elimination               true
% 3.78/1.01  --inst_learning_loop_flag               true
% 3.78/1.01  --inst_learning_start                   3000
% 3.78/1.01  --inst_learning_factor                  2
% 3.78/1.01  --inst_start_prop_sim_after_learn       3
% 3.78/1.01  --inst_sel_renew                        solver
% 3.78/1.01  --inst_lit_activity_flag                true
% 3.78/1.01  --inst_restr_to_given                   false
% 3.78/1.01  --inst_activity_threshold               500
% 3.78/1.01  --inst_out_proof                        true
% 3.78/1.01  
% 3.78/1.01  ------ Resolution Options
% 3.78/1.01  
% 3.78/1.01  --resolution_flag                       true
% 3.78/1.01  --res_lit_sel                           adaptive
% 3.78/1.01  --res_lit_sel_side                      none
% 3.78/1.01  --res_ordering                          kbo
% 3.78/1.01  --res_to_prop_solver                    active
% 3.78/1.01  --res_prop_simpl_new                    false
% 3.78/1.01  --res_prop_simpl_given                  true
% 3.78/1.01  --res_passive_queue_type                priority_queues
% 3.78/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/1.01  --res_passive_queues_freq               [15;5]
% 3.78/1.01  --res_forward_subs                      full
% 3.78/1.01  --res_backward_subs                     full
% 3.78/1.01  --res_forward_subs_resolution           true
% 3.78/1.01  --res_backward_subs_resolution          true
% 3.78/1.01  --res_orphan_elimination                true
% 3.78/1.01  --res_time_limit                        2.
% 3.78/1.01  --res_out_proof                         true
% 3.78/1.01  
% 3.78/1.01  ------ Superposition Options
% 3.78/1.01  
% 3.78/1.01  --superposition_flag                    true
% 3.78/1.01  --sup_passive_queue_type                priority_queues
% 3.78/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.78/1.01  --demod_completeness_check              fast
% 3.78/1.01  --demod_use_ground                      true
% 3.78/1.01  --sup_to_prop_solver                    passive
% 3.78/1.01  --sup_prop_simpl_new                    true
% 3.78/1.01  --sup_prop_simpl_given                  true
% 3.78/1.01  --sup_fun_splitting                     true
% 3.78/1.01  --sup_smt_interval                      50000
% 3.78/1.01  
% 3.78/1.01  ------ Superposition Simplification Setup
% 3.78/1.01  
% 3.78/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.78/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.78/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.78/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.78/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.78/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.78/1.01  --sup_immed_triv                        [TrivRules]
% 3.78/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/1.01  --sup_immed_bw_main                     []
% 3.78/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.78/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/1.01  --sup_input_bw                          []
% 3.78/1.01  
% 3.78/1.01  ------ Combination Options
% 3.78/1.01  
% 3.78/1.01  --comb_res_mult                         3
% 3.78/1.01  --comb_sup_mult                         2
% 3.78/1.01  --comb_inst_mult                        10
% 3.78/1.01  
% 3.78/1.01  ------ Debug Options
% 3.78/1.01  
% 3.78/1.01  --dbg_backtrace                         false
% 3.78/1.01  --dbg_dump_prop_clauses                 false
% 3.78/1.01  --dbg_dump_prop_clauses_file            -
% 3.78/1.01  --dbg_out_stat                          false
% 3.78/1.01  ------ Parsing...
% 3.78/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/1.01  
% 3.78/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.78/1.01  
% 3.78/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/1.01  
% 3.78/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.01  ------ Proving...
% 3.78/1.01  ------ Problem Properties 
% 3.78/1.01  
% 3.78/1.01  
% 3.78/1.01  clauses                                 15
% 3.78/1.01  conjectures                             3
% 3.78/1.01  EPR                                     1
% 3.78/1.01  Horn                                    14
% 3.78/1.01  unary                                   8
% 3.78/1.01  binary                                  3
% 3.78/1.01  lits                                    27
% 3.78/1.01  lits eq                                 3
% 3.78/1.01  fd_pure                                 0
% 3.78/1.01  fd_pseudo                               0
% 3.78/1.01  fd_cond                                 0
% 3.78/1.01  fd_pseudo_cond                          0
% 3.78/1.01  AC symbols                              0
% 3.78/1.01  
% 3.78/1.01  ------ Schedule dynamic 5 is on 
% 3.78/1.01  
% 3.78/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.78/1.01  
% 3.78/1.01  
% 3.78/1.01  ------ 
% 3.78/1.01  Current options:
% 3.78/1.01  ------ 
% 3.78/1.01  
% 3.78/1.01  ------ Input Options
% 3.78/1.01  
% 3.78/1.01  --out_options                           all
% 3.78/1.01  --tptp_safe_out                         true
% 3.78/1.01  --problem_path                          ""
% 3.78/1.01  --include_path                          ""
% 3.78/1.01  --clausifier                            res/vclausify_rel
% 3.78/1.01  --clausifier_options                    ""
% 3.78/1.01  --stdin                                 false
% 3.78/1.01  --stats_out                             all
% 3.78/1.01  
% 3.78/1.01  ------ General Options
% 3.78/1.01  
% 3.78/1.01  --fof                                   false
% 3.78/1.01  --time_out_real                         305.
% 3.78/1.01  --time_out_virtual                      -1.
% 3.78/1.01  --symbol_type_check                     false
% 3.78/1.01  --clausify_out                          false
% 3.78/1.01  --sig_cnt_out                           false
% 3.78/1.01  --trig_cnt_out                          false
% 3.78/1.01  --trig_cnt_out_tolerance                1.
% 3.78/1.01  --trig_cnt_out_sk_spl                   false
% 3.78/1.01  --abstr_cl_out                          false
% 3.78/1.01  
% 3.78/1.01  ------ Global Options
% 3.78/1.01  
% 3.78/1.01  --schedule                              default
% 3.78/1.01  --add_important_lit                     false
% 3.78/1.01  --prop_solver_per_cl                    1000
% 3.78/1.01  --min_unsat_core                        false
% 3.78/1.01  --soft_assumptions                      false
% 3.78/1.01  --soft_lemma_size                       3
% 3.78/1.01  --prop_impl_unit_size                   0
% 3.78/1.01  --prop_impl_unit                        []
% 3.78/1.01  --share_sel_clauses                     true
% 3.78/1.01  --reset_solvers                         false
% 3.78/1.01  --bc_imp_inh                            [conj_cone]
% 3.78/1.01  --conj_cone_tolerance                   3.
% 3.78/1.01  --extra_neg_conj                        none
% 3.78/1.01  --large_theory_mode                     true
% 3.78/1.01  --prolific_symb_bound                   200
% 3.78/1.01  --lt_threshold                          2000
% 3.78/1.01  --clause_weak_htbl                      true
% 3.78/1.01  --gc_record_bc_elim                     false
% 3.78/1.01  
% 3.78/1.01  ------ Preprocessing Options
% 3.78/1.01  
% 3.78/1.01  --preprocessing_flag                    true
% 3.78/1.01  --time_out_prep_mult                    0.1
% 3.78/1.01  --splitting_mode                        input
% 3.78/1.01  --splitting_grd                         true
% 3.78/1.01  --splitting_cvd                         false
% 3.78/1.01  --splitting_cvd_svl                     false
% 3.78/1.01  --splitting_nvd                         32
% 3.78/1.01  --sub_typing                            true
% 3.78/1.01  --prep_gs_sim                           true
% 3.78/1.01  --prep_unflatten                        true
% 3.78/1.01  --prep_res_sim                          true
% 3.78/1.01  --prep_upred                            true
% 3.78/1.01  --prep_sem_filter                       exhaustive
% 3.78/1.01  --prep_sem_filter_out                   false
% 3.78/1.01  --pred_elim                             true
% 3.78/1.01  --res_sim_input                         true
% 3.78/1.01  --eq_ax_congr_red                       true
% 3.78/1.01  --pure_diseq_elim                       true
% 3.78/1.01  --brand_transform                       false
% 3.78/1.01  --non_eq_to_eq                          false
% 3.78/1.01  --prep_def_merge                        true
% 3.78/1.01  --prep_def_merge_prop_impl              false
% 3.78/1.01  --prep_def_merge_mbd                    true
% 3.78/1.01  --prep_def_merge_tr_red                 false
% 3.78/1.01  --prep_def_merge_tr_cl                  false
% 3.78/1.01  --smt_preprocessing                     true
% 3.78/1.01  --smt_ac_axioms                         fast
% 3.78/1.01  --preprocessed_out                      false
% 3.78/1.01  --preprocessed_stats                    false
% 3.78/1.01  
% 3.78/1.01  ------ Abstraction refinement Options
% 3.78/1.01  
% 3.78/1.01  --abstr_ref                             []
% 3.78/1.01  --abstr_ref_prep                        false
% 3.78/1.01  --abstr_ref_until_sat                   false
% 3.78/1.01  --abstr_ref_sig_restrict                funpre
% 3.78/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/1.01  --abstr_ref_under                       []
% 3.78/1.01  
% 3.78/1.01  ------ SAT Options
% 3.78/1.01  
% 3.78/1.01  --sat_mode                              false
% 3.78/1.01  --sat_fm_restart_options                ""
% 3.78/1.01  --sat_gr_def                            false
% 3.78/1.01  --sat_epr_types                         true
% 3.78/1.01  --sat_non_cyclic_types                  false
% 3.78/1.01  --sat_finite_models                     false
% 3.78/1.01  --sat_fm_lemmas                         false
% 3.78/1.01  --sat_fm_prep                           false
% 3.78/1.01  --sat_fm_uc_incr                        true
% 3.78/1.01  --sat_out_model                         small
% 3.78/1.01  --sat_out_clauses                       false
% 3.78/1.01  
% 3.78/1.01  ------ QBF Options
% 3.78/1.01  
% 3.78/1.01  --qbf_mode                              false
% 3.78/1.01  --qbf_elim_univ                         false
% 3.78/1.01  --qbf_dom_inst                          none
% 3.78/1.01  --qbf_dom_pre_inst                      false
% 3.78/1.01  --qbf_sk_in                             false
% 3.78/1.01  --qbf_pred_elim                         true
% 3.78/1.01  --qbf_split                             512
% 3.78/1.01  
% 3.78/1.01  ------ BMC1 Options
% 3.78/1.01  
% 3.78/1.01  --bmc1_incremental                      false
% 3.78/1.01  --bmc1_axioms                           reachable_all
% 3.78/1.01  --bmc1_min_bound                        0
% 3.78/1.01  --bmc1_max_bound                        -1
% 3.78/1.01  --bmc1_max_bound_default                -1
% 3.78/1.01  --bmc1_symbol_reachability              true
% 3.78/1.01  --bmc1_property_lemmas                  false
% 3.78/1.01  --bmc1_k_induction                      false
% 3.78/1.01  --bmc1_non_equiv_states                 false
% 3.78/1.01  --bmc1_deadlock                         false
% 3.78/1.01  --bmc1_ucm                              false
% 3.78/1.01  --bmc1_add_unsat_core                   none
% 3.78/1.01  --bmc1_unsat_core_children              false
% 3.78/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/1.01  --bmc1_out_stat                         full
% 3.78/1.01  --bmc1_ground_init                      false
% 3.78/1.01  --bmc1_pre_inst_next_state              false
% 3.78/1.01  --bmc1_pre_inst_state                   false
% 3.78/1.01  --bmc1_pre_inst_reach_state             false
% 3.78/1.01  --bmc1_out_unsat_core                   false
% 3.78/1.01  --bmc1_aig_witness_out                  false
% 3.78/1.01  --bmc1_verbose                          false
% 3.78/1.01  --bmc1_dump_clauses_tptp                false
% 3.78/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.78/1.01  --bmc1_dump_file                        -
% 3.78/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.78/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.78/1.01  --bmc1_ucm_extend_mode                  1
% 3.78/1.01  --bmc1_ucm_init_mode                    2
% 3.78/1.01  --bmc1_ucm_cone_mode                    none
% 3.78/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.78/1.01  --bmc1_ucm_relax_model                  4
% 3.78/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.78/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/1.01  --bmc1_ucm_layered_model                none
% 3.78/1.01  --bmc1_ucm_max_lemma_size               10
% 3.78/1.01  
% 3.78/1.01  ------ AIG Options
% 3.78/1.01  
% 3.78/1.01  --aig_mode                              false
% 3.78/1.01  
% 3.78/1.01  ------ Instantiation Options
% 3.78/1.01  
% 3.78/1.01  --instantiation_flag                    true
% 3.78/1.01  --inst_sos_flag                         true
% 3.78/1.01  --inst_sos_phase                        true
% 3.78/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/1.01  --inst_lit_sel_side                     none
% 3.78/1.01  --inst_solver_per_active                1400
% 3.78/1.01  --inst_solver_calls_frac                1.
% 3.78/1.01  --inst_passive_queue_type               priority_queues
% 3.78/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/1.01  --inst_passive_queues_freq              [25;2]
% 3.78/1.01  --inst_dismatching                      true
% 3.78/1.01  --inst_eager_unprocessed_to_passive     true
% 3.78/1.01  --inst_prop_sim_given                   true
% 3.78/1.01  --inst_prop_sim_new                     false
% 3.78/1.01  --inst_subs_new                         false
% 3.78/1.01  --inst_eq_res_simp                      false
% 3.78/1.01  --inst_subs_given                       false
% 3.78/1.01  --inst_orphan_elimination               true
% 3.78/1.01  --inst_learning_loop_flag               true
% 3.78/1.01  --inst_learning_start                   3000
% 3.78/1.01  --inst_learning_factor                  2
% 3.78/1.01  --inst_start_prop_sim_after_learn       3
% 3.78/1.01  --inst_sel_renew                        solver
% 3.78/1.01  --inst_lit_activity_flag                true
% 3.78/1.01  --inst_restr_to_given                   false
% 3.78/1.01  --inst_activity_threshold               500
% 3.78/1.01  --inst_out_proof                        true
% 3.78/1.01  
% 3.78/1.01  ------ Resolution Options
% 3.78/1.01  
% 3.78/1.01  --resolution_flag                       false
% 3.78/1.01  --res_lit_sel                           adaptive
% 3.78/1.01  --res_lit_sel_side                      none
% 3.78/1.01  --res_ordering                          kbo
% 3.78/1.01  --res_to_prop_solver                    active
% 3.78/1.01  --res_prop_simpl_new                    false
% 3.78/1.01  --res_prop_simpl_given                  true
% 3.78/1.01  --res_passive_queue_type                priority_queues
% 3.78/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/1.01  --res_passive_queues_freq               [15;5]
% 3.78/1.01  --res_forward_subs                      full
% 3.78/1.01  --res_backward_subs                     full
% 3.78/1.01  --res_forward_subs_resolution           true
% 3.78/1.01  --res_backward_subs_resolution          true
% 3.78/1.01  --res_orphan_elimination                true
% 3.78/1.01  --res_time_limit                        2.
% 3.78/1.01  --res_out_proof                         true
% 3.78/1.01  
% 3.78/1.01  ------ Superposition Options
% 3.78/1.01  
% 3.78/1.01  --superposition_flag                    true
% 3.78/1.01  --sup_passive_queue_type                priority_queues
% 3.78/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.78/1.01  --demod_completeness_check              fast
% 3.78/1.01  --demod_use_ground                      true
% 3.78/1.01  --sup_to_prop_solver                    passive
% 3.78/1.01  --sup_prop_simpl_new                    true
% 3.78/1.01  --sup_prop_simpl_given                  true
% 3.78/1.01  --sup_fun_splitting                     true
% 3.78/1.01  --sup_smt_interval                      50000
% 3.78/1.01  
% 3.78/1.01  ------ Superposition Simplification Setup
% 3.78/1.01  
% 3.78/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.78/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.78/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.78/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.78/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.78/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.78/1.01  --sup_immed_triv                        [TrivRules]
% 3.78/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/1.01  --sup_immed_bw_main                     []
% 3.78/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.78/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/1.01  --sup_input_bw                          []
% 3.78/1.01  
% 3.78/1.01  ------ Combination Options
% 3.78/1.01  
% 3.78/1.01  --comb_res_mult                         3
% 3.78/1.01  --comb_sup_mult                         2
% 3.78/1.01  --comb_inst_mult                        10
% 3.78/1.01  
% 3.78/1.01  ------ Debug Options
% 3.78/1.01  
% 3.78/1.01  --dbg_backtrace                         false
% 3.78/1.01  --dbg_dump_prop_clauses                 false
% 3.78/1.01  --dbg_dump_prop_clauses_file            -
% 3.78/1.01  --dbg_out_stat                          false
% 3.78/1.01  
% 3.78/1.01  
% 3.78/1.01  
% 3.78/1.01  
% 3.78/1.01  ------ Proving...
% 3.78/1.01  
% 3.78/1.01  
% 3.78/1.01  % SZS status Theorem for theBenchmark.p
% 3.78/1.01  
% 3.78/1.01   Resolution empty clause
% 3.78/1.01  
% 3.78/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/1.01  
% 3.78/1.01  fof(f2,axiom,(
% 3.78/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.01  
% 3.78/1.01  fof(f33,plain,(
% 3.78/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.78/1.01    inference(cnf_transformation,[],[f2])).
% 3.78/1.01  
% 3.78/1.01  fof(f7,conjecture,(
% 3.78/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 3.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.01  
% 3.78/1.01  fof(f8,negated_conjecture,(
% 3.78/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 3.78/1.01    inference(negated_conjecture,[],[f7])).
% 3.78/1.01  
% 3.78/1.01  fof(f18,plain,(
% 3.78/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.78/1.01    inference(ennf_transformation,[],[f8])).
% 3.78/1.01  
% 3.78/1.01  fof(f19,plain,(
% 3.78/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.78/1.01    inference(flattening,[],[f18])).
% 3.78/1.01  
% 3.78/1.01  fof(f28,plain,(
% 3.78/1.01    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.78/1.01    introduced(choice_axiom,[])).
% 3.78/1.01  
% 3.78/1.01  fof(f27,plain,(
% 3.78/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.78/1.01    introduced(choice_axiom,[])).
% 3.78/1.01  
% 3.78/1.01  fof(f26,plain,(
% 3.78/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.78/1.01    introduced(choice_axiom,[])).
% 3.78/1.01  
% 3.78/1.01  fof(f25,plain,(
% 3.78/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.78/1.01    introduced(choice_axiom,[])).
% 3.78/1.01  
% 3.78/1.01  fof(f29,plain,(
% 3.78/1.01    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.78/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f28,f27,f26,f25])).
% 3.78/1.01  
% 3.78/1.01  fof(f43,plain,(
% 3.78/1.01    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.78/1.01    inference(cnf_transformation,[],[f29])).
% 3.78/1.01  
% 3.78/1.01  fof(f44,plain,(
% 3.78/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.78/1.01    inference(cnf_transformation,[],[f29])).
% 3.78/1.01  
% 3.78/1.01  fof(f4,axiom,(
% 3.78/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.01  
% 3.78/1.01  fof(f12,plain,(
% 3.78/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.78/1.01    inference(ennf_transformation,[],[f4])).
% 3.78/1.01  
% 3.78/1.01  fof(f13,plain,(
% 3.78/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/1.01    inference(flattening,[],[f12])).
% 3.78/1.01  
% 3.78/1.01  fof(f35,plain,(
% 3.78/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.78/1.01    inference(cnf_transformation,[],[f13])).
% 3.78/1.01  
% 3.78/1.01  fof(f3,axiom,(
% 3.78/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.01  
% 3.78/1.01  fof(f10,plain,(
% 3.78/1.01    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.78/1.01    inference(ennf_transformation,[],[f3])).
% 3.78/1.01  
% 3.78/1.01  fof(f11,plain,(
% 3.78/1.01    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.78/1.01    inference(flattening,[],[f10])).
% 3.78/1.01  
% 3.78/1.01  fof(f34,plain,(
% 3.78/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.78/1.01    inference(cnf_transformation,[],[f11])).
% 3.78/1.01  
% 3.78/1.01  fof(f5,axiom,(
% 3.78/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.01  
% 3.78/1.01  fof(f14,plain,(
% 3.78/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.78/1.01    inference(ennf_transformation,[],[f5])).
% 3.78/1.01  
% 3.78/1.01  fof(f15,plain,(
% 3.78/1.01    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.78/1.01    inference(flattening,[],[f14])).
% 3.78/1.01  
% 3.78/1.01  fof(f36,plain,(
% 3.78/1.01    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.78/1.01    inference(cnf_transformation,[],[f15])).
% 3.78/1.01  
% 3.78/1.01  fof(f41,plain,(
% 3.78/1.01    l1_pre_topc(sK1)),
% 3.78/1.01    inference(cnf_transformation,[],[f29])).
% 3.78/1.01  
% 3.78/1.01  fof(f45,plain,(
% 3.78/1.01    m1_connsp_2(sK3,sK1,sK2)),
% 3.78/1.01    inference(cnf_transformation,[],[f29])).
% 3.78/1.01  
% 3.78/1.01  fof(f6,axiom,(
% 3.78/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.01  
% 3.78/1.01  fof(f16,plain,(
% 3.78/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.78/1.01    inference(ennf_transformation,[],[f6])).
% 3.78/1.01  
% 3.78/1.01  fof(f17,plain,(
% 3.78/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/1.01    inference(flattening,[],[f16])).
% 3.78/1.01  
% 3.78/1.01  fof(f24,plain,(
% 3.78/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/1.01    inference(nnf_transformation,[],[f17])).
% 3.78/1.01  
% 3.78/1.01  fof(f37,plain,(
% 3.78/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.01    inference(cnf_transformation,[],[f24])).
% 3.78/1.01  
% 3.78/1.01  fof(f40,plain,(
% 3.78/1.01    v2_pre_topc(sK1)),
% 3.78/1.01    inference(cnf_transformation,[],[f29])).
% 3.78/1.01  
% 3.78/1.01  fof(f39,plain,(
% 3.78/1.01    ~v2_struct_0(sK1)),
% 3.78/1.01    inference(cnf_transformation,[],[f29])).
% 3.78/1.01  
% 3.78/1.01  fof(f42,plain,(
% 3.78/1.01    m1_subset_1(sK2,u1_struct_0(sK1))),
% 3.78/1.01    inference(cnf_transformation,[],[f29])).
% 3.78/1.01  
% 3.78/1.01  fof(f1,axiom,(
% 3.78/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.01  
% 3.78/1.01  fof(f9,plain,(
% 3.78/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.78/1.01    inference(ennf_transformation,[],[f1])).
% 3.78/1.01  
% 3.78/1.01  fof(f20,plain,(
% 3.78/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/1.01    inference(nnf_transformation,[],[f9])).
% 3.78/1.01  
% 3.78/1.01  fof(f21,plain,(
% 3.78/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/1.01    inference(rectify,[],[f20])).
% 3.78/1.01  
% 3.78/1.01  fof(f22,plain,(
% 3.78/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.78/1.01    introduced(choice_axiom,[])).
% 3.78/1.01  
% 3.78/1.01  fof(f23,plain,(
% 3.78/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.78/1.01  
% 3.78/1.01  fof(f30,plain,(
% 3.78/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.78/1.01    inference(cnf_transformation,[],[f23])).
% 3.78/1.01  
% 3.78/1.01  fof(f47,plain,(
% 3.78/1.01    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 3.78/1.01    inference(cnf_transformation,[],[f29])).
% 3.78/1.01  
% 3.78/1.01  fof(f38,plain,(
% 3.78/1.01    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.01    inference(cnf_transformation,[],[f24])).
% 3.78/1.01  
% 3.78/1.01  cnf(c_3,plain,
% 3.78/1.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.78/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_448,plain,
% 3.78/1.01      ( r1_tarski(X0_45,k2_xboole_0(X0_45,X1_45)) ),
% 3.78/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_700,plain,
% 3.78/1.01      ( r1_tarski(X0_45,k2_xboole_0(X0_45,X1_45)) = iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_13,negated_conjecture,
% 3.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.78/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_444,negated_conjecture,
% 3.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.78/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_704,plain,
% 3.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_12,negated_conjecture,
% 3.78/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.78/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_445,negated_conjecture,
% 3.78/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.78/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_703,plain,
% 3.78/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_5,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.78/1.01      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.78/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_446,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
% 3.78/1.01      | ~ m1_subset_1(X1_45,k1_zfmisc_1(X0_46))
% 3.78/1.01      | k4_subset_1(X0_46,X1_45,X0_45) = k2_xboole_0(X1_45,X0_45) ),
% 3.78/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_702,plain,
% 3.78/1.01      ( k4_subset_1(X0_46,X0_45,X1_45) = k2_xboole_0(X0_45,X1_45)
% 3.78/1.01      | m1_subset_1(X0_45,k1_zfmisc_1(X0_46)) != iProver_top
% 3.78/1.01      | m1_subset_1(X1_45,k1_zfmisc_1(X0_46)) != iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_1586,plain,
% 3.78/1.01      ( k4_subset_1(u1_struct_0(sK1),X0_45,sK4) = k2_xboole_0(X0_45,sK4)
% 3.78/1.01      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.78/1.01      inference(superposition,[status(thm)],[c_703,c_702]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_2014,plain,
% 3.78/1.01      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 3.78/1.01      inference(superposition,[status(thm)],[c_704,c_1586]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_4,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.78/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.78/1.01      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.78/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_447,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
% 3.78/1.01      | ~ m1_subset_1(X1_45,k1_zfmisc_1(X0_46))
% 3.78/1.01      | m1_subset_1(k4_subset_1(X0_46,X1_45,X0_45),k1_zfmisc_1(X0_46)) ),
% 3.78/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_701,plain,
% 3.78/1.01      ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46)) != iProver_top
% 3.78/1.01      | m1_subset_1(X1_45,k1_zfmisc_1(X0_46)) != iProver_top
% 3.78/1.01      | m1_subset_1(k4_subset_1(X0_46,X0_45,X1_45),k1_zfmisc_1(X0_46)) = iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_6,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.01      | ~ r1_tarski(X2,X0)
% 3.78/1.01      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 3.78/1.01      | ~ l1_pre_topc(X1) ),
% 3.78/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_15,negated_conjecture,
% 3.78/1.01      ( l1_pre_topc(sK1) ),
% 3.78/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_251,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.01      | ~ r1_tarski(X2,X0)
% 3.78/1.01      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 3.78/1.01      | sK1 != X1 ),
% 3.78/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_252,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ r1_tarski(X1,X0)
% 3.78/1.01      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 3.78/1.01      inference(unflattening,[status(thm)],[c_251]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_442,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ r1_tarski(X1_45,X0_45)
% 3.78/1.01      | r1_tarski(k1_tops_1(sK1,X1_45),k1_tops_1(sK1,X0_45)) ),
% 3.78/1.01      inference(subtyping,[status(esa)],[c_252]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_706,plain,
% 3.78/1.01      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | r1_tarski(X1_45,X0_45) != iProver_top
% 3.78/1.01      | r1_tarski(k1_tops_1(sK1,X1_45),k1_tops_1(sK1,X0_45)) = iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_11,negated_conjecture,
% 3.78/1.01      ( m1_connsp_2(sK3,sK1,sK2) ),
% 3.78/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_8,plain,
% 3.78/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 3.78/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.01      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.78/1.01      | v2_struct_0(X1)
% 3.78/1.01      | ~ v2_pre_topc(X1)
% 3.78/1.01      | ~ l1_pre_topc(X1) ),
% 3.78/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_16,negated_conjecture,
% 3.78/1.01      ( v2_pre_topc(sK1) ),
% 3.78/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_193,plain,
% 3.78/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 3.78/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.01      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.78/1.01      | v2_struct_0(X1)
% 3.78/1.01      | ~ l1_pre_topc(X1)
% 3.78/1.01      | sK1 != X1 ),
% 3.78/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_194,plain,
% 3.78/1.01      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.78/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 3.78/1.01      | v2_struct_0(sK1)
% 3.78/1.01      | ~ l1_pre_topc(sK1) ),
% 3.78/1.01      inference(unflattening,[status(thm)],[c_193]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_17,negated_conjecture,
% 3.78/1.01      ( ~ v2_struct_0(sK1) ),
% 3.78/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_198,plain,
% 3.78/1.01      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.78/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 3.78/1.01      inference(global_propositional_subsumption,
% 3.78/1.01                [status(thm)],
% 3.78/1.01                [c_194,c_17,c_15]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_320,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 3.78/1.01      | sK2 != X0
% 3.78/1.01      | sK3 != X1
% 3.78/1.01      | sK1 != sK1 ),
% 3.78/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_198]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_321,plain,
% 3.78/1.01      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.78/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.78/1.01      inference(unflattening,[status(thm)],[c_320]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_14,negated_conjecture,
% 3.78/1.01      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.78/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_323,plain,
% 3.78/1.01      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.78/1.01      inference(global_propositional_subsumption,
% 3.78/1.01                [status(thm)],
% 3.78/1.01                [c_321,c_14,c_13]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_439,plain,
% 3.78/1.01      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 3.78/1.01      inference(subtyping,[status(esa)],[c_323]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_709,plain,
% 3.78/1.01      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_2,plain,
% 3.78/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.78/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_449,plain,
% 3.78/1.01      ( ~ r2_hidden(X0_45,X1_45)
% 3.78/1.01      | r2_hidden(X0_45,X2_45)
% 3.78/1.01      | ~ r1_tarski(X1_45,X2_45) ),
% 3.78/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_699,plain,
% 3.78/1.01      ( r2_hidden(X0_45,X1_45) != iProver_top
% 3.78/1.01      | r2_hidden(X0_45,X2_45) = iProver_top
% 3.78/1.01      | r1_tarski(X1_45,X2_45) != iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_1270,plain,
% 3.78/1.01      ( r2_hidden(sK2,X0_45) = iProver_top
% 3.78/1.01      | r1_tarski(k1_tops_1(sK1,sK3),X0_45) != iProver_top ),
% 3.78/1.01      inference(superposition,[status(thm)],[c_709,c_699]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_1346,plain,
% 3.78/1.01      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | r2_hidden(sK2,k1_tops_1(sK1,X0_45)) = iProver_top
% 3.78/1.01      | r1_tarski(sK3,X0_45) != iProver_top ),
% 3.78/1.01      inference(superposition,[status(thm)],[c_706,c_1270]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_22,plain,
% 3.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_1420,plain,
% 3.78/1.01      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | r2_hidden(sK2,k1_tops_1(sK1,X0_45)) = iProver_top
% 3.78/1.01      | r1_tarski(sK3,X0_45) != iProver_top ),
% 3.78/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1346,c_22]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_1428,plain,
% 3.78/1.01      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0_45,X1_45))) = iProver_top
% 3.78/1.01      | r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),X0_45,X1_45)) != iProver_top ),
% 3.78/1.01      inference(superposition,[status(thm)],[c_701,c_1420]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_2596,plain,
% 3.78/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = iProver_top
% 3.78/1.01      | r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != iProver_top ),
% 3.78/1.01      inference(superposition,[status(thm)],[c_2014,c_1428]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_2604,plain,
% 3.78/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = iProver_top
% 3.78/1.01      | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
% 3.78/1.01      inference(light_normalisation,[status(thm)],[c_2596,c_2014]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_23,plain,
% 3.78/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_9,negated_conjecture,
% 3.78/1.01      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 3.78/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_7,plain,
% 3.78/1.01      ( m1_connsp_2(X0,X1,X2)
% 3.78/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.01      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.78/1.01      | v2_struct_0(X1)
% 3.78/1.01      | ~ v2_pre_topc(X1)
% 3.78/1.01      | ~ l1_pre_topc(X1) ),
% 3.78/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_217,plain,
% 3.78/1.01      ( m1_connsp_2(X0,X1,X2)
% 3.78/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.01      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.78/1.01      | v2_struct_0(X1)
% 3.78/1.01      | ~ l1_pre_topc(X1)
% 3.78/1.01      | sK1 != X1 ),
% 3.78/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_218,plain,
% 3.78/1.01      ( m1_connsp_2(X0,sK1,X1)
% 3.78/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 3.78/1.01      | v2_struct_0(sK1)
% 3.78/1.01      | ~ l1_pre_topc(sK1) ),
% 3.78/1.01      inference(unflattening,[status(thm)],[c_217]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_222,plain,
% 3.78/1.01      ( m1_connsp_2(X0,sK1,X1)
% 3.78/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 3.78/1.01      inference(global_propositional_subsumption,
% 3.78/1.01                [status(thm)],
% 3.78/1.01                [c_218,c_17,c_15]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_295,plain,
% 3.78/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 3.78/1.01      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 3.78/1.01      | sK2 != X0
% 3.78/1.01      | sK1 != sK1 ),
% 3.78/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_222]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_296,plain,
% 3.78/1.01      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.78/1.01      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 3.78/1.01      inference(unflattening,[status(thm)],[c_295]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_298,plain,
% 3.78/1.01      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 3.78/1.01      inference(global_propositional_subsumption,[status(thm)],[c_296,c_14]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_441,plain,
% 3.78/1.01      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 3.78/1.01      inference(subtyping,[status(esa)],[c_298]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_707,plain,
% 3.78/1.01      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_21,plain,
% 3.78/1.01      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_297,plain,
% 3.78/1.01      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.78/1.01      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_730,plain,
% 3.78/1.01      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.78/1.01      inference(instantiation,[status(thm)],[c_447]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_731,plain,
% 3.78/1.01      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.78/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.01      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.78/1.01      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_957,plain,
% 3.78/1.01      ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 3.78/1.01      inference(global_propositional_subsumption,
% 3.78/1.01                [status(thm)],
% 3.78/1.01                [c_707,c_21,c_22,c_23,c_297,c_731]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_2129,plain,
% 3.78/1.01      ( r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) != iProver_top ),
% 3.78/1.01      inference(demodulation,[status(thm)],[c_2014,c_957]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_11121,plain,
% 3.78/1.01      ( r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
% 3.78/1.01      inference(global_propositional_subsumption,
% 3.78/1.01                [status(thm)],
% 3.78/1.01                [c_2604,c_22,c_23,c_2129]) ).
% 3.78/1.01  
% 3.78/1.01  cnf(c_11125,plain,
% 3.78/1.01      ( $false ),
% 3.78/1.01      inference(superposition,[status(thm)],[c_700,c_11121]) ).
% 3.78/1.01  
% 3.78/1.01  
% 3.78/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/1.01  
% 3.78/1.01  ------                               Statistics
% 3.78/1.01  
% 3.78/1.01  ------ General
% 3.78/1.01  
% 3.78/1.01  abstr_ref_over_cycles:                  0
% 3.78/1.01  abstr_ref_under_cycles:                 0
% 3.78/1.01  gc_basic_clause_elim:                   0
% 3.78/1.01  forced_gc_time:                         0
% 3.78/1.01  parsing_time:                           0.01
% 3.78/1.01  unif_index_cands_time:                  0.
% 3.78/1.01  unif_index_add_time:                    0.
% 3.78/1.01  orderings_time:                         0.
% 3.78/1.01  out_proof_time:                         0.01
% 3.78/1.01  total_time:                             0.438
% 3.78/1.01  num_of_symbols:                         51
% 3.78/1.01  num_of_terms:                           17150
% 3.78/1.01  
% 3.78/1.01  ------ Preprocessing
% 3.78/1.01  
% 3.78/1.01  num_of_splits:                          0
% 3.78/1.01  num_of_split_atoms:                     0
% 3.78/1.01  num_of_reused_defs:                     0
% 3.78/1.01  num_eq_ax_congr_red:                    19
% 3.78/1.01  num_of_sem_filtered_clauses:            1
% 3.78/1.01  num_of_subtypes:                        3
% 3.78/1.01  monotx_restored_types:                  0
% 3.78/1.01  sat_num_of_epr_types:                   0
% 3.78/1.01  sat_num_of_non_cyclic_types:            0
% 3.78/1.01  sat_guarded_non_collapsed_types:        0
% 3.78/1.01  num_pure_diseq_elim:                    0
% 3.78/1.01  simp_replaced_by:                       0
% 3.78/1.01  res_preprocessed:                       78
% 3.78/1.01  prep_upred:                             0
% 3.78/1.01  prep_unflattend:                        9
% 3.78/1.01  smt_new_axioms:                         0
% 3.78/1.01  pred_elim_cands:                        3
% 3.78/1.01  pred_elim:                              4
% 3.78/1.01  pred_elim_cl:                           3
% 3.78/1.01  pred_elim_cycles:                       6
% 3.78/1.01  merged_defs:                            0
% 3.78/1.01  merged_defs_ncl:                        0
% 3.78/1.01  bin_hyper_res:                          0
% 3.78/1.01  prep_cycles:                            4
% 3.78/1.01  pred_elim_time:                         0.003
% 3.78/1.01  splitting_time:                         0.
% 3.78/1.01  sem_filter_time:                        0.
% 3.78/1.01  monotx_time:                            0.
% 3.78/1.01  subtype_inf_time:                       0.
% 3.78/1.01  
% 3.78/1.01  ------ Problem properties
% 3.78/1.01  
% 3.78/1.01  clauses:                                15
% 3.78/1.01  conjectures:                            3
% 3.78/1.01  epr:                                    1
% 3.78/1.01  horn:                                   14
% 3.78/1.01  ground:                                 8
% 3.78/1.01  unary:                                  8
% 3.78/1.01  binary:                                 3
% 3.78/1.01  lits:                                   27
% 3.78/1.01  lits_eq:                                3
% 3.78/1.01  fd_pure:                                0
% 3.78/1.01  fd_pseudo:                              0
% 3.78/1.01  fd_cond:                                0
% 3.78/1.01  fd_pseudo_cond:                         0
% 3.78/1.01  ac_symbols:                             0
% 3.78/1.01  
% 3.78/1.01  ------ Propositional Solver
% 3.78/1.01  
% 3.78/1.01  prop_solver_calls:                      32
% 3.78/1.01  prop_fast_solver_calls:                 695
% 3.78/1.01  smt_solver_calls:                       0
% 3.78/1.01  smt_fast_solver_calls:                  0
% 3.78/1.01  prop_num_of_clauses:                    5118
% 3.78/1.01  prop_preprocess_simplified:             7248
% 3.78/1.01  prop_fo_subsumed:                       42
% 3.78/1.01  prop_solver_time:                       0.
% 3.78/1.01  smt_solver_time:                        0.
% 3.78/1.01  smt_fast_solver_time:                   0.
% 3.78/1.01  prop_fast_solver_time:                  0.
% 3.78/1.01  prop_unsat_core_time:                   0.
% 3.78/1.01  
% 3.78/1.01  ------ QBF
% 3.78/1.01  
% 3.78/1.01  qbf_q_res:                              0
% 3.78/1.01  qbf_num_tautologies:                    0
% 3.78/1.01  qbf_prep_cycles:                        0
% 3.78/1.01  
% 3.78/1.01  ------ BMC1
% 3.78/1.01  
% 3.78/1.01  bmc1_current_bound:                     -1
% 3.78/1.01  bmc1_last_solved_bound:                 -1
% 3.78/1.01  bmc1_unsat_core_size:                   -1
% 3.78/1.01  bmc1_unsat_core_parents_size:           -1
% 3.78/1.01  bmc1_merge_next_fun:                    0
% 3.78/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.78/1.01  
% 3.78/1.01  ------ Instantiation
% 3.78/1.01  
% 3.78/1.01  inst_num_of_clauses:                    1236
% 3.78/1.01  inst_num_in_passive:                    179
% 3.78/1.01  inst_num_in_active:                     671
% 3.78/1.01  inst_num_in_unprocessed:                386
% 3.78/1.01  inst_num_of_loops:                      790
% 3.78/1.01  inst_num_of_learning_restarts:          0
% 3.78/1.01  inst_num_moves_active_passive:          115
% 3.78/1.01  inst_lit_activity:                      0
% 3.78/1.01  inst_lit_activity_moves:                1
% 3.78/1.01  inst_num_tautologies:                   0
% 3.78/1.01  inst_num_prop_implied:                  0
% 3.78/1.01  inst_num_existing_simplified:           0
% 3.78/1.01  inst_num_eq_res_simplified:             0
% 3.78/1.01  inst_num_child_elim:                    0
% 3.78/1.01  inst_num_of_dismatching_blockings:      2267
% 3.78/1.01  inst_num_of_non_proper_insts:           1648
% 3.78/1.01  inst_num_of_duplicates:                 0
% 3.78/1.01  inst_inst_num_from_inst_to_res:         0
% 3.78/1.01  inst_dismatching_checking_time:         0.
% 3.78/1.01  
% 3.78/1.01  ------ Resolution
% 3.78/1.01  
% 3.78/1.01  res_num_of_clauses:                     0
% 3.78/1.01  res_num_in_passive:                     0
% 3.78/1.01  res_num_in_active:                      0
% 3.78/1.01  res_num_of_loops:                       82
% 3.78/1.01  res_forward_subset_subsumed:            70
% 3.78/1.01  res_backward_subset_subsumed:           0
% 3.78/1.01  res_forward_subsumed:                   0
% 3.78/1.01  res_backward_subsumed:                  0
% 3.78/1.01  res_forward_subsumption_resolution:     0
% 3.78/1.01  res_backward_subsumption_resolution:    0
% 3.78/1.01  res_clause_to_clause_subsumption:       1876
% 3.78/1.01  res_orphan_elimination:                 0
% 3.78/1.01  res_tautology_del:                      31
% 3.78/1.01  res_num_eq_res_simplified:              2
% 3.78/1.01  res_num_sel_changes:                    0
% 3.78/1.01  res_moves_from_active_to_pass:          0
% 3.78/1.01  
% 3.78/1.01  ------ Superposition
% 3.78/1.01  
% 3.78/1.01  sup_time_total:                         0.
% 3.78/1.01  sup_time_generating:                    0.
% 3.78/1.01  sup_time_sim_full:                      0.
% 3.78/1.01  sup_time_sim_immed:                     0.
% 3.78/1.01  
% 3.78/1.01  sup_num_of_clauses:                     691
% 3.78/1.01  sup_num_in_active:                      147
% 3.78/1.01  sup_num_in_passive:                     544
% 3.78/1.01  sup_num_of_loops:                       157
% 3.78/1.01  sup_fw_superposition:                   368
% 3.78/1.01  sup_bw_superposition:                   378
% 3.78/1.01  sup_immediate_simplified:               390
% 3.78/1.01  sup_given_eliminated:                   0
% 3.78/1.01  comparisons_done:                       0
% 3.78/1.01  comparisons_avoided:                    0
% 3.78/1.01  
% 3.78/1.01  ------ Simplifications
% 3.78/1.01  
% 3.78/1.01  
% 3.78/1.01  sim_fw_subset_subsumed:                 4
% 3.78/1.01  sim_bw_subset_subsumed:                 0
% 3.78/1.01  sim_fw_subsumed:                        1
% 3.78/1.01  sim_bw_subsumed:                        0
% 3.78/1.01  sim_fw_subsumption_res:                 0
% 3.78/1.01  sim_bw_subsumption_res:                 0
% 3.78/1.01  sim_tautology_del:                      1
% 3.78/1.01  sim_eq_tautology_del:                   34
% 3.78/1.01  sim_eq_res_simp:                        0
% 3.78/1.01  sim_fw_demodulated:                     0
% 3.78/1.01  sim_bw_demodulated:                     11
% 3.78/1.01  sim_light_normalised:                   389
% 3.78/1.01  sim_joinable_taut:                      0
% 3.78/1.01  sim_joinable_simp:                      0
% 3.78/1.01  sim_ac_normalised:                      0
% 3.78/1.01  sim_smt_subsumption:                    0
% 3.78/1.01  
%------------------------------------------------------------------------------

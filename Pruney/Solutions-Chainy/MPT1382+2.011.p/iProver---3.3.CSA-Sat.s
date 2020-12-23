%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:17 EST 2020

% Result     : CounterSatisfiable 1.65s
% Output     : Saturation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  152 (1052 expanded)
%              Number of clauses        :  103 ( 316 expanded)
%              Number of leaves         :   21 ( 308 expanded)
%              Depth                    :   22
%              Number of atoms          :  543 (8111 expanded)
%              Number of equality atoms :  140 ( 318 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_233,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_231,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_230,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_228,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_223,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_603,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_915,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_917,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1347,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_917])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_912,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_1035,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_915,c_912])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_919,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1238,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1035,c_919])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_920,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1504,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_920])).

cnf(c_1892,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),X0) = X0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_919])).

cnf(c_1987,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1347,c_1892])).

cnf(c_2102,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1987,c_920])).

cnf(c_2222,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),X0) = X0
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2102,c_919])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_911,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_1085,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_915,c_911])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_918,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_278,plain,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v1_xboole_0(X0)
    | k1_tops_1(X2,X1) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_279,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_283,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
    | v1_xboole_0(k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_16,c_15])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_105,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_10])).

cnf(c_106,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_105])).

cnf(c_337,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_106,c_16])).

cnf(c_338,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(X1,k1_tops_1(sK0,X0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_342,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_17,c_15])).

cnf(c_447,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v1_xboole_0(X2)
    | X1 != X3
    | k1_tops_1(sK0,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_342])).

cnf(c_448,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v1_xboole_0(k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_466,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(resolution,[status(thm)],[c_283,c_448])).

cnf(c_358,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_359,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_17,c_15])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
    | ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_466,c_363])).

cnf(c_471,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(renaming,[status(thm)],[c_470])).

cnf(c_910,plain,
    ( m1_connsp_2(X0,sK0,X1) != iProver_top
    | m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_1355,plain,
    ( m1_connsp_2(X0,sK0,X1) != iProver_top
    | m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_910])).

cnf(c_1766,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X0) != iProver_top
    | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_1355])).

cnf(c_1767,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X0) != iProver_top
    | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1766,c_1085])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_992,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_1038,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1015,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK0))
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_1086,plain,
    ( m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK0))
    | k2_xboole_0(k1_tops_1(sK0,sK2),sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_1127,plain,
    ( m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_xboole_0(k1_tops_1(sK0,sK2),sK2) != sK2
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_1129,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) != sK2
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_604,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1128,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_1191,plain,
    ( ~ m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1192,plain,
    ( m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1191])).

cnf(c_1280,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0)
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1486,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_1487,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_1230,plain,
    ( m1_connsp_2(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),sK0,sK1) != iProver_top
    | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_910])).

cnf(c_1231,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X0) != iProver_top
    | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1230,c_1085])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,plain,
    ( m1_connsp_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_993,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_1003,plain,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_1058,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_1059,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
    | m1_connsp_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1058])).

cnf(c_1672,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1231,c_21,c_22,c_23,c_993,c_1059])).

cnf(c_1673,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1672])).

cnf(c_1678,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_1673])).

cnf(c_2107,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1767,c_13,c_22,c_992,c_1038,c_1129,c_1128,c_1192,c_1487,c_1678])).

cnf(c_1354,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_912])).

cnf(c_1563,plain,
    ( k2_xboole_0(k1_tops_1(sK0,X0),X0) = X0
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_919])).

cnf(c_1992,plain,
    ( k2_xboole_0(k1_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),k1_tops_1(sK0,u1_struct_0(sK0))) = k1_tops_1(sK0,u1_struct_0(sK0))
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1563])).

cnf(c_1562,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_1354])).

cnf(c_1665,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1562,c_13,c_22,c_992,c_1038,c_1129,c_1128,c_1192,c_1487])).

cnf(c_1670,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_1665,c_919])).

cnf(c_1353,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_911])).

cnf(c_1580,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0)))) = k1_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0)))
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1353])).

cnf(c_1452,plain,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1347,c_919])).

cnf(c_1509,plain,
    ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_920])).

cnf(c_913,plain,
    ( m1_connsp_2(X0,sK0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_916,plain,
    ( m1_connsp_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_914,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:23:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.65/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/0.96  
% 1.65/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.65/0.96  
% 1.65/0.96  ------  iProver source info
% 1.65/0.96  
% 1.65/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.65/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.65/0.96  git: non_committed_changes: false
% 1.65/0.96  git: last_make_outside_of_git: false
% 1.65/0.96  
% 1.65/0.96  ------ 
% 1.65/0.96  
% 1.65/0.96  ------ Input Options
% 1.65/0.96  
% 1.65/0.96  --out_options                           all
% 1.65/0.96  --tptp_safe_out                         true
% 1.65/0.96  --problem_path                          ""
% 1.65/0.96  --include_path                          ""
% 1.65/0.96  --clausifier                            res/vclausify_rel
% 1.65/0.96  --clausifier_options                    --mode clausify
% 1.65/0.96  --stdin                                 false
% 1.65/0.96  --stats_out                             all
% 1.65/0.96  
% 1.65/0.96  ------ General Options
% 1.65/0.96  
% 1.65/0.96  --fof                                   false
% 1.65/0.96  --time_out_real                         305.
% 1.65/0.96  --time_out_virtual                      -1.
% 1.65/0.96  --symbol_type_check                     false
% 1.65/0.96  --clausify_out                          false
% 1.65/0.96  --sig_cnt_out                           false
% 1.65/0.96  --trig_cnt_out                          false
% 1.65/0.96  --trig_cnt_out_tolerance                1.
% 1.65/0.96  --trig_cnt_out_sk_spl                   false
% 1.65/0.96  --abstr_cl_out                          false
% 1.65/0.96  
% 1.65/0.96  ------ Global Options
% 1.65/0.96  
% 1.65/0.96  --schedule                              default
% 1.65/0.96  --add_important_lit                     false
% 1.65/0.96  --prop_solver_per_cl                    1000
% 1.65/0.96  --min_unsat_core                        false
% 1.65/0.96  --soft_assumptions                      false
% 1.65/0.96  --soft_lemma_size                       3
% 1.65/0.96  --prop_impl_unit_size                   0
% 1.65/0.96  --prop_impl_unit                        []
% 1.65/0.96  --share_sel_clauses                     true
% 1.65/0.96  --reset_solvers                         false
% 1.65/0.96  --bc_imp_inh                            [conj_cone]
% 1.65/0.96  --conj_cone_tolerance                   3.
% 1.65/0.96  --extra_neg_conj                        none
% 1.65/0.96  --large_theory_mode                     true
% 1.65/0.96  --prolific_symb_bound                   200
% 1.65/0.96  --lt_threshold                          2000
% 1.65/0.96  --clause_weak_htbl                      true
% 1.65/0.96  --gc_record_bc_elim                     false
% 1.65/0.96  
% 1.65/0.96  ------ Preprocessing Options
% 1.65/0.96  
% 1.65/0.96  --preprocessing_flag                    true
% 1.65/0.96  --time_out_prep_mult                    0.1
% 1.65/0.96  --splitting_mode                        input
% 1.65/0.96  --splitting_grd                         true
% 1.65/0.96  --splitting_cvd                         false
% 1.65/0.96  --splitting_cvd_svl                     false
% 1.65/0.96  --splitting_nvd                         32
% 1.65/0.96  --sub_typing                            true
% 1.65/0.96  --prep_gs_sim                           true
% 1.65/0.96  --prep_unflatten                        true
% 1.65/0.96  --prep_res_sim                          true
% 1.65/0.96  --prep_upred                            true
% 1.65/0.96  --prep_sem_filter                       exhaustive
% 1.65/0.96  --prep_sem_filter_out                   false
% 1.65/0.96  --pred_elim                             true
% 1.65/0.96  --res_sim_input                         true
% 1.65/0.96  --eq_ax_congr_red                       true
% 1.65/0.96  --pure_diseq_elim                       true
% 1.65/0.96  --brand_transform                       false
% 1.65/0.96  --non_eq_to_eq                          false
% 1.65/0.96  --prep_def_merge                        true
% 1.65/0.96  --prep_def_merge_prop_impl              false
% 1.65/0.96  --prep_def_merge_mbd                    true
% 1.65/0.96  --prep_def_merge_tr_red                 false
% 1.65/0.96  --prep_def_merge_tr_cl                  false
% 1.65/0.96  --smt_preprocessing                     true
% 1.65/0.96  --smt_ac_axioms                         fast
% 1.65/0.96  --preprocessed_out                      false
% 1.65/0.96  --preprocessed_stats                    false
% 1.65/0.96  
% 1.65/0.96  ------ Abstraction refinement Options
% 1.65/0.96  
% 1.65/0.96  --abstr_ref                             []
% 1.65/0.96  --abstr_ref_prep                        false
% 1.65/0.96  --abstr_ref_until_sat                   false
% 1.65/0.96  --abstr_ref_sig_restrict                funpre
% 1.65/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/0.96  --abstr_ref_under                       []
% 1.65/0.96  
% 1.65/0.96  ------ SAT Options
% 1.65/0.96  
% 1.65/0.96  --sat_mode                              false
% 1.65/0.96  --sat_fm_restart_options                ""
% 1.65/0.96  --sat_gr_def                            false
% 1.65/0.96  --sat_epr_types                         true
% 1.65/0.96  --sat_non_cyclic_types                  false
% 1.65/0.96  --sat_finite_models                     false
% 1.65/0.96  --sat_fm_lemmas                         false
% 1.65/0.96  --sat_fm_prep                           false
% 1.65/0.96  --sat_fm_uc_incr                        true
% 1.65/0.96  --sat_out_model                         small
% 1.65/0.96  --sat_out_clauses                       false
% 1.65/0.96  
% 1.65/0.96  ------ QBF Options
% 1.65/0.96  
% 1.65/0.96  --qbf_mode                              false
% 1.65/0.96  --qbf_elim_univ                         false
% 1.65/0.96  --qbf_dom_inst                          none
% 1.65/0.96  --qbf_dom_pre_inst                      false
% 1.65/0.96  --qbf_sk_in                             false
% 1.65/0.96  --qbf_pred_elim                         true
% 1.65/0.96  --qbf_split                             512
% 1.65/0.96  
% 1.65/0.96  ------ BMC1 Options
% 1.65/0.96  
% 1.65/0.96  --bmc1_incremental                      false
% 1.65/0.96  --bmc1_axioms                           reachable_all
% 1.65/0.96  --bmc1_min_bound                        0
% 1.65/0.96  --bmc1_max_bound                        -1
% 1.65/0.96  --bmc1_max_bound_default                -1
% 1.65/0.96  --bmc1_symbol_reachability              true
% 1.65/0.96  --bmc1_property_lemmas                  false
% 1.65/0.96  --bmc1_k_induction                      false
% 1.65/0.96  --bmc1_non_equiv_states                 false
% 1.65/0.96  --bmc1_deadlock                         false
% 1.65/0.96  --bmc1_ucm                              false
% 1.65/0.96  --bmc1_add_unsat_core                   none
% 1.65/0.96  --bmc1_unsat_core_children              false
% 1.65/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/0.96  --bmc1_out_stat                         full
% 1.65/0.96  --bmc1_ground_init                      false
% 1.65/0.96  --bmc1_pre_inst_next_state              false
% 1.65/0.96  --bmc1_pre_inst_state                   false
% 1.65/0.96  --bmc1_pre_inst_reach_state             false
% 1.65/0.96  --bmc1_out_unsat_core                   false
% 1.65/0.96  --bmc1_aig_witness_out                  false
% 1.65/0.96  --bmc1_verbose                          false
% 1.65/0.96  --bmc1_dump_clauses_tptp                false
% 1.65/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.65/0.96  --bmc1_dump_file                        -
% 1.65/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.65/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.65/0.96  --bmc1_ucm_extend_mode                  1
% 1.65/0.96  --bmc1_ucm_init_mode                    2
% 1.65/0.96  --bmc1_ucm_cone_mode                    none
% 1.65/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.65/0.96  --bmc1_ucm_relax_model                  4
% 1.65/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.65/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/0.96  --bmc1_ucm_layered_model                none
% 1.65/0.96  --bmc1_ucm_max_lemma_size               10
% 1.65/0.96  
% 1.65/0.96  ------ AIG Options
% 1.65/0.96  
% 1.65/0.96  --aig_mode                              false
% 1.65/0.96  
% 1.65/0.96  ------ Instantiation Options
% 1.65/0.96  
% 1.65/0.96  --instantiation_flag                    true
% 1.65/0.96  --inst_sos_flag                         false
% 1.65/0.96  --inst_sos_phase                        true
% 1.65/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/0.96  --inst_lit_sel_side                     num_symb
% 1.65/0.96  --inst_solver_per_active                1400
% 1.65/0.96  --inst_solver_calls_frac                1.
% 1.65/0.96  --inst_passive_queue_type               priority_queues
% 1.65/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/0.96  --inst_passive_queues_freq              [25;2]
% 1.65/0.96  --inst_dismatching                      true
% 1.65/0.96  --inst_eager_unprocessed_to_passive     true
% 1.65/0.96  --inst_prop_sim_given                   true
% 1.65/0.96  --inst_prop_sim_new                     false
% 1.65/0.96  --inst_subs_new                         false
% 1.65/0.96  --inst_eq_res_simp                      false
% 1.65/0.96  --inst_subs_given                       false
% 1.65/0.96  --inst_orphan_elimination               true
% 1.65/0.96  --inst_learning_loop_flag               true
% 1.65/0.96  --inst_learning_start                   3000
% 1.65/0.96  --inst_learning_factor                  2
% 1.65/0.96  --inst_start_prop_sim_after_learn       3
% 1.65/0.96  --inst_sel_renew                        solver
% 1.65/0.96  --inst_lit_activity_flag                true
% 1.65/0.96  --inst_restr_to_given                   false
% 1.65/0.96  --inst_activity_threshold               500
% 1.65/0.96  --inst_out_proof                        true
% 1.65/0.96  
% 1.65/0.96  ------ Resolution Options
% 1.65/0.96  
% 1.65/0.96  --resolution_flag                       true
% 1.65/0.96  --res_lit_sel                           adaptive
% 1.65/0.96  --res_lit_sel_side                      none
% 1.65/0.96  --res_ordering                          kbo
% 1.65/0.96  --res_to_prop_solver                    active
% 1.65/0.96  --res_prop_simpl_new                    false
% 1.65/0.96  --res_prop_simpl_given                  true
% 1.65/0.96  --res_passive_queue_type                priority_queues
% 1.65/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/0.96  --res_passive_queues_freq               [15;5]
% 1.65/0.96  --res_forward_subs                      full
% 1.65/0.96  --res_backward_subs                     full
% 1.65/0.96  --res_forward_subs_resolution           true
% 1.65/0.96  --res_backward_subs_resolution          true
% 1.65/0.96  --res_orphan_elimination                true
% 1.65/0.96  --res_time_limit                        2.
% 1.65/0.96  --res_out_proof                         true
% 1.65/0.96  
% 1.65/0.96  ------ Superposition Options
% 1.65/0.96  
% 1.65/0.96  --superposition_flag                    true
% 1.65/0.96  --sup_passive_queue_type                priority_queues
% 1.65/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.65/0.96  --demod_completeness_check              fast
% 1.65/0.96  --demod_use_ground                      true
% 1.65/0.96  --sup_to_prop_solver                    passive
% 1.65/0.96  --sup_prop_simpl_new                    true
% 1.65/0.96  --sup_prop_simpl_given                  true
% 1.65/0.96  --sup_fun_splitting                     false
% 1.65/0.96  --sup_smt_interval                      50000
% 1.65/0.96  
% 1.65/0.96  ------ Superposition Simplification Setup
% 1.65/0.96  
% 1.65/0.96  --sup_indices_passive                   []
% 1.65/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.96  --sup_full_bw                           [BwDemod]
% 1.65/0.96  --sup_immed_triv                        [TrivRules]
% 1.65/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.96  --sup_immed_bw_main                     []
% 1.65/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/0.96  
% 1.65/0.96  ------ Combination Options
% 1.65/0.96  
% 1.65/0.96  --comb_res_mult                         3
% 1.65/0.96  --comb_sup_mult                         2
% 1.65/0.96  --comb_inst_mult                        10
% 1.65/0.96  
% 1.65/0.96  ------ Debug Options
% 1.65/0.96  
% 1.65/0.96  --dbg_backtrace                         false
% 1.65/0.96  --dbg_dump_prop_clauses                 false
% 1.65/0.96  --dbg_dump_prop_clauses_file            -
% 1.65/0.96  --dbg_out_stat                          false
% 1.65/0.96  ------ Parsing...
% 1.65/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.65/0.96  
% 1.65/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.65/0.96  
% 1.65/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.65/0.96  
% 1.65/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.65/0.96  ------ Proving...
% 1.65/0.96  ------ Problem Properties 
% 1.65/0.96  
% 1.65/0.96  
% 1.65/0.96  clauses                                 11
% 1.65/0.96  conjectures                             3
% 1.65/0.96  EPR                                     1
% 1.65/0.96  Horn                                    11
% 1.65/0.96  unary                                   3
% 1.65/0.96  binary                                  6
% 1.65/0.96  lits                                    23
% 1.65/0.96  lits eq                                 2
% 1.65/0.96  fd_pure                                 0
% 1.65/0.96  fd_pseudo                               0
% 1.65/0.96  fd_cond                                 0
% 1.65/0.96  fd_pseudo_cond                          0
% 1.65/0.96  AC symbols                              0
% 1.65/0.96  
% 1.65/0.96  ------ Schedule dynamic 5 is on 
% 1.65/0.96  
% 1.65/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.65/0.96  
% 1.65/0.96  
% 1.65/0.96  ------ 
% 1.65/0.96  Current options:
% 1.65/0.96  ------ 
% 1.65/0.96  
% 1.65/0.96  ------ Input Options
% 1.65/0.96  
% 1.65/0.96  --out_options                           all
% 1.65/0.96  --tptp_safe_out                         true
% 1.65/0.96  --problem_path                          ""
% 1.65/0.96  --include_path                          ""
% 1.65/0.96  --clausifier                            res/vclausify_rel
% 1.65/0.96  --clausifier_options                    --mode clausify
% 1.65/0.96  --stdin                                 false
% 1.65/0.96  --stats_out                             all
% 1.65/0.96  
% 1.65/0.96  ------ General Options
% 1.65/0.96  
% 1.65/0.96  --fof                                   false
% 1.65/0.96  --time_out_real                         305.
% 1.65/0.96  --time_out_virtual                      -1.
% 1.65/0.96  --symbol_type_check                     false
% 1.65/0.96  --clausify_out                          false
% 1.65/0.96  --sig_cnt_out                           false
% 1.65/0.96  --trig_cnt_out                          false
% 1.65/0.96  --trig_cnt_out_tolerance                1.
% 1.65/0.96  --trig_cnt_out_sk_spl                   false
% 1.65/0.96  --abstr_cl_out                          false
% 1.65/0.96  
% 1.65/0.96  ------ Global Options
% 1.65/0.96  
% 1.65/0.96  --schedule                              default
% 1.65/0.96  --add_important_lit                     false
% 1.65/0.96  --prop_solver_per_cl                    1000
% 1.65/0.96  --min_unsat_core                        false
% 1.65/0.96  --soft_assumptions                      false
% 1.65/0.96  --soft_lemma_size                       3
% 1.65/0.96  --prop_impl_unit_size                   0
% 1.65/0.96  --prop_impl_unit                        []
% 1.65/0.96  --share_sel_clauses                     true
% 1.65/0.96  --reset_solvers                         false
% 1.65/0.96  --bc_imp_inh                            [conj_cone]
% 1.65/0.96  --conj_cone_tolerance                   3.
% 1.65/0.96  --extra_neg_conj                        none
% 1.65/0.96  --large_theory_mode                     true
% 1.65/0.96  --prolific_symb_bound                   200
% 1.65/0.96  --lt_threshold                          2000
% 1.65/0.96  --clause_weak_htbl                      true
% 1.65/0.96  --gc_record_bc_elim                     false
% 1.65/0.96  
% 1.65/0.96  ------ Preprocessing Options
% 1.65/0.96  
% 1.65/0.96  --preprocessing_flag                    true
% 1.65/0.96  --time_out_prep_mult                    0.1
% 1.65/0.96  --splitting_mode                        input
% 1.65/0.96  --splitting_grd                         true
% 1.65/0.96  --splitting_cvd                         false
% 1.65/0.96  --splitting_cvd_svl                     false
% 1.65/0.96  --splitting_nvd                         32
% 1.65/0.96  --sub_typing                            true
% 1.65/0.96  --prep_gs_sim                           true
% 1.65/0.96  --prep_unflatten                        true
% 1.65/0.96  --prep_res_sim                          true
% 1.65/0.96  --prep_upred                            true
% 1.65/0.96  --prep_sem_filter                       exhaustive
% 1.65/0.96  --prep_sem_filter_out                   false
% 1.65/0.96  --pred_elim                             true
% 1.65/0.96  --res_sim_input                         true
% 1.65/0.96  --eq_ax_congr_red                       true
% 1.65/0.96  --pure_diseq_elim                       true
% 1.65/0.96  --brand_transform                       false
% 1.65/0.96  --non_eq_to_eq                          false
% 1.65/0.96  --prep_def_merge                        true
% 1.65/0.96  --prep_def_merge_prop_impl              false
% 1.65/0.96  --prep_def_merge_mbd                    true
% 1.65/0.96  --prep_def_merge_tr_red                 false
% 1.65/0.96  --prep_def_merge_tr_cl                  false
% 1.65/0.96  --smt_preprocessing                     true
% 1.65/0.96  --smt_ac_axioms                         fast
% 1.65/0.96  --preprocessed_out                      false
% 1.65/0.96  --preprocessed_stats                    false
% 1.65/0.96  
% 1.65/0.96  ------ Abstraction refinement Options
% 1.65/0.96  
% 1.65/0.96  --abstr_ref                             []
% 1.65/0.96  --abstr_ref_prep                        false
% 1.65/0.96  --abstr_ref_until_sat                   false
% 1.65/0.96  --abstr_ref_sig_restrict                funpre
% 1.65/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/0.96  --abstr_ref_under                       []
% 1.65/0.96  
% 1.65/0.96  ------ SAT Options
% 1.65/0.96  
% 1.65/0.96  --sat_mode                              false
% 1.65/0.96  --sat_fm_restart_options                ""
% 1.65/0.96  --sat_gr_def                            false
% 1.65/0.96  --sat_epr_types                         true
% 1.65/0.96  --sat_non_cyclic_types                  false
% 1.65/0.96  --sat_finite_models                     false
% 1.65/0.96  --sat_fm_lemmas                         false
% 1.65/0.96  --sat_fm_prep                           false
% 1.65/0.96  --sat_fm_uc_incr                        true
% 1.65/0.96  --sat_out_model                         small
% 1.65/0.96  --sat_out_clauses                       false
% 1.65/0.96  
% 1.65/0.96  ------ QBF Options
% 1.65/0.96  
% 1.65/0.96  --qbf_mode                              false
% 1.65/0.96  --qbf_elim_univ                         false
% 1.65/0.96  --qbf_dom_inst                          none
% 1.65/0.96  --qbf_dom_pre_inst                      false
% 1.65/0.96  --qbf_sk_in                             false
% 1.65/0.96  --qbf_pred_elim                         true
% 1.65/0.96  --qbf_split                             512
% 1.65/0.96  
% 1.65/0.96  ------ BMC1 Options
% 1.65/0.96  
% 1.65/0.96  --bmc1_incremental                      false
% 1.65/0.96  --bmc1_axioms                           reachable_all
% 1.65/0.96  --bmc1_min_bound                        0
% 1.65/0.96  --bmc1_max_bound                        -1
% 1.65/0.96  --bmc1_max_bound_default                -1
% 1.65/0.96  --bmc1_symbol_reachability              true
% 1.65/0.96  --bmc1_property_lemmas                  false
% 1.65/0.96  --bmc1_k_induction                      false
% 1.65/0.96  --bmc1_non_equiv_states                 false
% 1.65/0.96  --bmc1_deadlock                         false
% 1.65/0.96  --bmc1_ucm                              false
% 1.65/0.96  --bmc1_add_unsat_core                   none
% 1.65/0.96  --bmc1_unsat_core_children              false
% 1.65/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/0.96  --bmc1_out_stat                         full
% 1.65/0.96  --bmc1_ground_init                      false
% 1.65/0.96  --bmc1_pre_inst_next_state              false
% 1.65/0.96  --bmc1_pre_inst_state                   false
% 1.65/0.96  --bmc1_pre_inst_reach_state             false
% 1.65/0.96  --bmc1_out_unsat_core                   false
% 1.65/0.96  --bmc1_aig_witness_out                  false
% 1.65/0.96  --bmc1_verbose                          false
% 1.65/0.96  --bmc1_dump_clauses_tptp                false
% 1.65/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.65/0.96  --bmc1_dump_file                        -
% 1.65/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.65/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.65/0.96  --bmc1_ucm_extend_mode                  1
% 1.65/0.96  --bmc1_ucm_init_mode                    2
% 1.65/0.96  --bmc1_ucm_cone_mode                    none
% 1.65/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.65/0.96  --bmc1_ucm_relax_model                  4
% 1.65/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.65/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/0.96  --bmc1_ucm_layered_model                none
% 1.65/0.96  --bmc1_ucm_max_lemma_size               10
% 1.65/0.96  
% 1.65/0.96  ------ AIG Options
% 1.65/0.96  
% 1.65/0.96  --aig_mode                              false
% 1.65/0.96  
% 1.65/0.96  ------ Instantiation Options
% 1.65/0.96  
% 1.65/0.96  --instantiation_flag                    true
% 1.65/0.96  --inst_sos_flag                         false
% 1.65/0.96  --inst_sos_phase                        true
% 1.65/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/0.96  --inst_lit_sel_side                     none
% 1.65/0.96  --inst_solver_per_active                1400
% 1.65/0.96  --inst_solver_calls_frac                1.
% 1.65/0.96  --inst_passive_queue_type               priority_queues
% 1.65/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/0.96  --inst_passive_queues_freq              [25;2]
% 1.65/0.96  --inst_dismatching                      true
% 1.65/0.96  --inst_eager_unprocessed_to_passive     true
% 1.65/0.96  --inst_prop_sim_given                   true
% 1.65/0.96  --inst_prop_sim_new                     false
% 1.65/0.96  --inst_subs_new                         false
% 1.65/0.96  --inst_eq_res_simp                      false
% 1.65/0.96  --inst_subs_given                       false
% 1.65/0.96  --inst_orphan_elimination               true
% 1.65/0.96  --inst_learning_loop_flag               true
% 1.65/0.96  --inst_learning_start                   3000
% 1.65/0.96  --inst_learning_factor                  2
% 1.65/0.96  --inst_start_prop_sim_after_learn       3
% 1.65/0.96  --inst_sel_renew                        solver
% 1.65/0.96  --inst_lit_activity_flag                true
% 1.65/0.96  --inst_restr_to_given                   false
% 1.65/0.96  --inst_activity_threshold               500
% 1.65/0.96  --inst_out_proof                        true
% 1.65/0.96  
% 1.65/0.96  ------ Resolution Options
% 1.65/0.96  
% 1.65/0.96  --resolution_flag                       false
% 1.65/0.96  --res_lit_sel                           adaptive
% 1.65/0.96  --res_lit_sel_side                      none
% 1.65/0.96  --res_ordering                          kbo
% 1.65/0.96  --res_to_prop_solver                    active
% 1.65/0.96  --res_prop_simpl_new                    false
% 1.65/0.96  --res_prop_simpl_given                  true
% 1.65/0.96  --res_passive_queue_type                priority_queues
% 1.65/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/0.96  --res_passive_queues_freq               [15;5]
% 1.65/0.96  --res_forward_subs                      full
% 1.65/0.96  --res_backward_subs                     full
% 1.65/0.96  --res_forward_subs_resolution           true
% 1.65/0.96  --res_backward_subs_resolution          true
% 1.65/0.96  --res_orphan_elimination                true
% 1.65/0.96  --res_time_limit                        2.
% 1.65/0.96  --res_out_proof                         true
% 1.65/0.96  
% 1.65/0.96  ------ Superposition Options
% 1.65/0.96  
% 1.65/0.96  --superposition_flag                    true
% 1.65/0.96  --sup_passive_queue_type                priority_queues
% 1.65/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.65/0.96  --demod_completeness_check              fast
% 1.65/0.96  --demod_use_ground                      true
% 1.65/0.96  --sup_to_prop_solver                    passive
% 1.65/0.96  --sup_prop_simpl_new                    true
% 1.65/0.96  --sup_prop_simpl_given                  true
% 1.65/0.96  --sup_fun_splitting                     false
% 1.65/0.96  --sup_smt_interval                      50000
% 1.65/0.96  
% 1.65/0.96  ------ Superposition Simplification Setup
% 1.65/0.96  
% 1.65/0.96  --sup_indices_passive                   []
% 1.65/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.96  --sup_full_bw                           [BwDemod]
% 1.65/0.96  --sup_immed_triv                        [TrivRules]
% 1.65/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.96  --sup_immed_bw_main                     []
% 1.65/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/0.96  
% 1.65/0.96  ------ Combination Options
% 1.65/0.96  
% 1.65/0.96  --comb_res_mult                         3
% 1.65/0.96  --comb_sup_mult                         2
% 1.65/0.96  --comb_inst_mult                        10
% 1.65/0.96  
% 1.65/0.96  ------ Debug Options
% 1.65/0.96  
% 1.65/0.96  --dbg_backtrace                         false
% 1.65/0.96  --dbg_dump_prop_clauses                 false
% 1.65/0.96  --dbg_dump_prop_clauses_file            -
% 1.65/0.96  --dbg_out_stat                          false
% 1.65/0.96  
% 1.65/0.96  
% 1.65/0.96  
% 1.65/0.96  
% 1.65/0.96  ------ Proving...
% 1.65/0.96  
% 1.65/0.96  
% 1.65/0.96  % SZS status CounterSatisfiable for theBenchmark.p
% 1.65/0.96  
% 1.65/0.96  % SZS output start Saturation for theBenchmark.p
% 1.65/0.96  
% 1.65/0.96  fof(f10,conjecture,(
% 1.65/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f11,negated_conjecture,(
% 1.65/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 1.65/0.96    inference(negated_conjecture,[],[f10])).
% 1.65/0.96  
% 1.65/0.96  fof(f25,plain,(
% 1.65/0.96    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.65/0.96    inference(ennf_transformation,[],[f11])).
% 1.65/0.96  
% 1.65/0.96  fof(f26,plain,(
% 1.65/0.96    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.65/0.96    inference(flattening,[],[f25])).
% 1.65/0.96  
% 1.65/0.96  fof(f31,plain,(
% 1.65/0.96    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.65/0.96    introduced(choice_axiom,[])).
% 1.65/0.96  
% 1.65/0.96  fof(f30,plain,(
% 1.65/0.96    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 1.65/0.96    introduced(choice_axiom,[])).
% 1.65/0.96  
% 1.65/0.96  fof(f29,plain,(
% 1.65/0.96    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.65/0.96    introduced(choice_axiom,[])).
% 1.65/0.96  
% 1.65/0.96  fof(f32,plain,(
% 1.65/0.96    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.65/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31,f30,f29])).
% 1.65/0.96  
% 1.65/0.96  fof(f48,plain,(
% 1.65/0.96    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.96    inference(cnf_transformation,[],[f32])).
% 1.65/0.96  
% 1.65/0.96  fof(f4,axiom,(
% 1.65/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f27,plain,(
% 1.65/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.65/0.96    inference(nnf_transformation,[],[f4])).
% 1.65/0.96  
% 1.65/0.96  fof(f36,plain,(
% 1.65/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.65/0.96    inference(cnf_transformation,[],[f27])).
% 1.65/0.96  
% 1.65/0.96  fof(f7,axiom,(
% 1.65/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f20,plain,(
% 1.65/0.96    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.96    inference(ennf_transformation,[],[f7])).
% 1.65/0.96  
% 1.65/0.96  fof(f40,plain,(
% 1.65/0.96    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f20])).
% 1.65/0.96  
% 1.65/0.96  fof(f46,plain,(
% 1.65/0.96    l1_pre_topc(sK0)),
% 1.65/0.96    inference(cnf_transformation,[],[f32])).
% 1.65/0.96  
% 1.65/0.96  fof(f3,axiom,(
% 1.65/0.96    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f15,plain,(
% 1.65/0.96    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.65/0.96    inference(ennf_transformation,[],[f3])).
% 1.65/0.96  
% 1.65/0.96  fof(f35,plain,(
% 1.65/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f15])).
% 1.65/0.96  
% 1.65/0.96  fof(f2,axiom,(
% 1.65/0.96    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f14,plain,(
% 1.65/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.65/0.96    inference(ennf_transformation,[],[f2])).
% 1.65/0.96  
% 1.65/0.96  fof(f34,plain,(
% 1.65/0.96    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f14])).
% 1.65/0.96  
% 1.65/0.96  fof(f6,axiom,(
% 1.65/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f18,plain,(
% 1.65/0.96    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.65/0.96    inference(ennf_transformation,[],[f6])).
% 1.65/0.96  
% 1.65/0.96  fof(f19,plain,(
% 1.65/0.96    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.65/0.96    inference(flattening,[],[f18])).
% 1.65/0.96  
% 1.65/0.96  fof(f39,plain,(
% 1.65/0.96    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f19])).
% 1.65/0.96  
% 1.65/0.96  fof(f37,plain,(
% 1.65/0.96    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f27])).
% 1.65/0.96  
% 1.65/0.96  fof(f5,axiom,(
% 1.65/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f16,plain,(
% 1.65/0.96    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.65/0.96    inference(ennf_transformation,[],[f5])).
% 1.65/0.96  
% 1.65/0.96  fof(f17,plain,(
% 1.65/0.96    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.96    inference(flattening,[],[f16])).
% 1.65/0.96  
% 1.65/0.96  fof(f38,plain,(
% 1.65/0.96    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f17])).
% 1.65/0.96  
% 1.65/0.96  fof(f50,plain,(
% 1.65/0.96    ( ! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f32])).
% 1.65/0.96  
% 1.65/0.96  fof(f45,plain,(
% 1.65/0.96    v2_pre_topc(sK0)),
% 1.65/0.96    inference(cnf_transformation,[],[f32])).
% 1.65/0.96  
% 1.65/0.96  fof(f1,axiom,(
% 1.65/0.96    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f12,plain,(
% 1.65/0.96    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.65/0.96    inference(unused_predicate_definition_removal,[],[f1])).
% 1.65/0.96  
% 1.65/0.96  fof(f13,plain,(
% 1.65/0.96    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.65/0.96    inference(ennf_transformation,[],[f12])).
% 1.65/0.96  
% 1.65/0.96  fof(f33,plain,(
% 1.65/0.96    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f13])).
% 1.65/0.96  
% 1.65/0.96  fof(f8,axiom,(
% 1.65/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f21,plain,(
% 1.65/0.96    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/0.96    inference(ennf_transformation,[],[f8])).
% 1.65/0.96  
% 1.65/0.96  fof(f22,plain,(
% 1.65/0.96    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/0.96    inference(flattening,[],[f21])).
% 1.65/0.96  
% 1.65/0.96  fof(f28,plain,(
% 1.65/0.96    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/0.96    inference(nnf_transformation,[],[f22])).
% 1.65/0.96  
% 1.65/0.96  fof(f41,plain,(
% 1.65/0.96    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f28])).
% 1.65/0.96  
% 1.65/0.96  fof(f9,axiom,(
% 1.65/0.96    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.65/0.96  
% 1.65/0.96  fof(f23,plain,(
% 1.65/0.96    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/0.96    inference(ennf_transformation,[],[f9])).
% 1.65/0.96  
% 1.65/0.96  fof(f24,plain,(
% 1.65/0.96    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/0.96    inference(flattening,[],[f23])).
% 1.65/0.96  
% 1.65/0.96  fof(f43,plain,(
% 1.65/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/0.96    inference(cnf_transformation,[],[f24])).
% 1.65/0.96  
% 1.65/0.96  fof(f44,plain,(
% 1.65/0.96    ~v2_struct_0(sK0)),
% 1.65/0.96    inference(cnf_transformation,[],[f32])).
% 1.65/0.96  
% 1.65/0.96  fof(f47,plain,(
% 1.65/0.96    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.65/0.96    inference(cnf_transformation,[],[f32])).
% 1.65/0.96  
% 1.65/0.96  fof(f49,plain,(
% 1.65/0.96    m1_connsp_2(sK2,sK0,sK1)),
% 1.65/0.96    inference(cnf_transformation,[],[f32])).
% 1.65/0.96  
% 1.65/0.96  cnf(c_233,plain,
% 1.65/0.96      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.65/0.96      theory(equality) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_231,plain,
% 1.65/0.96      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 1.65/0.96      theory(equality) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_230,plain,
% 1.65/0.96      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 1.65/0.96      theory(equality) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_228,plain,
% 1.65/0.96      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.65/0.96      theory(equality) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_223,plain,
% 1.65/0.96      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | X2 != X1 ),
% 1.65/0.96      theory(equality) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_603,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_13,negated_conjecture,
% 1.65/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.65/0.96      inference(cnf_transformation,[],[f48]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_915,plain,
% 1.65/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_4,plain,
% 1.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.65/0.96      inference(cnf_transformation,[],[f36]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_917,plain,
% 1.65/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.65/0.96      | r1_tarski(X0,X1) = iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1347,plain,
% 1.65/0.96      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_915,c_917]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_7,plain,
% 1.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.96      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.65/0.96      | ~ l1_pre_topc(X1) ),
% 1.65/0.96      inference(cnf_transformation,[],[f40]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_15,negated_conjecture,
% 1.65/0.96      ( l1_pre_topc(sK0) ),
% 1.65/0.96      inference(cnf_transformation,[],[f46]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_416,plain,
% 1.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.96      | r1_tarski(k1_tops_1(X1,X0),X0)
% 1.65/0.96      | sK0 != X1 ),
% 1.65/0.96      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_417,plain,
% 1.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 1.65/0.96      inference(unflattening,[status(thm)],[c_416]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_912,plain,
% 1.65/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1035,plain,
% 1.65/0.96      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_915,c_912]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_2,plain,
% 1.65/0.96      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.65/0.96      inference(cnf_transformation,[],[f35]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_919,plain,
% 1.65/0.96      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1238,plain,
% 1.65/0.96      ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_1035,c_919]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1,plain,
% 1.65/0.96      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 1.65/0.96      inference(cnf_transformation,[],[f34]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_920,plain,
% 1.65/0.96      ( r1_tarski(X0,X1) = iProver_top
% 1.65/0.96      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1504,plain,
% 1.65/0.96      ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
% 1.65/0.96      | r1_tarski(sK2,X0) != iProver_top ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_1238,c_920]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1892,plain,
% 1.65/0.96      ( k2_xboole_0(k1_tops_1(sK0,sK2),X0) = X0
% 1.65/0.96      | r1_tarski(sK2,X0) != iProver_top ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_1504,c_919]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1987,plain,
% 1.65/0.96      ( k2_xboole_0(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_1347,c_1892]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_2102,plain,
% 1.65/0.96      ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
% 1.65/0.96      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_1987,c_920]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_2222,plain,
% 1.65/0.96      ( k2_xboole_0(k1_tops_1(sK0,sK2),X0) = X0
% 1.65/0.96      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_2102,c_919]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_6,plain,
% 1.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.96      | ~ l1_pre_topc(X1)
% 1.65/0.96      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 1.65/0.96      inference(cnf_transformation,[],[f39]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_428,plain,
% 1.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.96      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 1.65/0.96      | sK0 != X1 ),
% 1.65/0.96      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_429,plain,
% 1.65/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 1.65/0.96      inference(unflattening,[status(thm)],[c_428]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_911,plain,
% 1.65/0.96      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 1.65/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1085,plain,
% 1.65/0.96      ( k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_915,c_911]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_3,plain,
% 1.65/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.65/0.96      inference(cnf_transformation,[],[f37]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_918,plain,
% 1.65/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.65/0.96      | r1_tarski(X0,X1) != iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_5,plain,
% 1.65/0.96      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 1.65/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.65/0.96      | ~ v2_pre_topc(X0)
% 1.65/0.96      | ~ l1_pre_topc(X0) ),
% 1.65/0.96      inference(cnf_transformation,[],[f38]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_11,negated_conjecture,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,sK1)
% 1.65/0.96      | ~ v3_pre_topc(X0,sK0)
% 1.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ r1_tarski(X0,sK2)
% 1.65/0.96      | v1_xboole_0(X0) ),
% 1.65/0.96      inference(cnf_transformation,[],[f50]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_278,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,sK1)
% 1.65/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ r1_tarski(X0,sK2)
% 1.65/0.96      | ~ v2_pre_topc(X2)
% 1.65/0.96      | ~ l1_pre_topc(X2)
% 1.65/0.96      | v1_xboole_0(X0)
% 1.65/0.96      | k1_tops_1(X2,X1) != X0
% 1.65/0.96      | sK0 != X2 ),
% 1.65/0.96      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_279,plain,
% 1.65/0.96      ( ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
% 1.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
% 1.65/0.96      | ~ v2_pre_topc(sK0)
% 1.65/0.96      | ~ l1_pre_topc(sK0)
% 1.65/0.96      | v1_xboole_0(k1_tops_1(sK0,X0)) ),
% 1.65/0.96      inference(unflattening,[status(thm)],[c_278]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_16,negated_conjecture,
% 1.65/0.96      ( v2_pre_topc(sK0) ),
% 1.65/0.96      inference(cnf_transformation,[],[f45]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_283,plain,
% 1.65/0.96      ( ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
% 1.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
% 1.65/0.96      | v1_xboole_0(k1_tops_1(sK0,X0)) ),
% 1.65/0.96      inference(global_propositional_subsumption,
% 1.65/0.96                [status(thm)],
% 1.65/0.96                [c_279,c_16,c_15]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_0,plain,
% 1.65/0.96      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.65/0.96      inference(cnf_transformation,[],[f33]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_9,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 1.65/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.96      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.65/0.96      | v2_struct_0(X1)
% 1.65/0.96      | ~ v2_pre_topc(X1)
% 1.65/0.96      | ~ l1_pre_topc(X1) ),
% 1.65/0.96      inference(cnf_transformation,[],[f41]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_10,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 1.65/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.96      | v2_struct_0(X1)
% 1.65/0.96      | ~ v2_pre_topc(X1)
% 1.65/0.96      | ~ l1_pre_topc(X1) ),
% 1.65/0.96      inference(cnf_transformation,[],[f43]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_105,plain,
% 1.65/0.96      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/0.96      | ~ m1_connsp_2(X0,X1,X2)
% 1.65/0.96      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.65/0.96      | v2_struct_0(X1)
% 1.65/0.96      | ~ v2_pre_topc(X1)
% 1.65/0.96      | ~ l1_pre_topc(X1) ),
% 1.65/0.96      inference(global_propositional_subsumption,[status(thm)],[c_9,c_10]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_106,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 1.65/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/0.96      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.65/0.96      | v2_struct_0(X1)
% 1.65/0.96      | ~ v2_pre_topc(X1)
% 1.65/0.96      | ~ l1_pre_topc(X1) ),
% 1.65/0.96      inference(renaming,[status(thm)],[c_105]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_337,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 1.65/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/0.96      | r2_hidden(X2,k1_tops_1(X1,X0))
% 1.65/0.96      | v2_struct_0(X1)
% 1.65/0.96      | ~ l1_pre_topc(X1)
% 1.65/0.96      | sK0 != X1 ),
% 1.65/0.96      inference(resolution_lifted,[status(thm)],[c_106,c_16]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_338,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.65/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.65/0.96      | r2_hidden(X1,k1_tops_1(sK0,X0))
% 1.65/0.96      | v2_struct_0(sK0)
% 1.65/0.96      | ~ l1_pre_topc(sK0) ),
% 1.65/0.96      inference(unflattening,[status(thm)],[c_337]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_17,negated_conjecture,
% 1.65/0.96      ( ~ v2_struct_0(sK0) ),
% 1.65/0.96      inference(cnf_transformation,[],[f44]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_342,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.65/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.65/0.96      | r2_hidden(X1,k1_tops_1(sK0,X0)) ),
% 1.65/0.96      inference(global_propositional_subsumption,
% 1.65/0.96                [status(thm)],
% 1.65/0.96                [c_338,c_17,c_15]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_447,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.65/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.65/0.96      | ~ v1_xboole_0(X2)
% 1.65/0.96      | X1 != X3
% 1.65/0.96      | k1_tops_1(sK0,X0) != X2 ),
% 1.65/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_342]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_448,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.65/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.65/0.96      | ~ v1_xboole_0(k1_tops_1(sK0,X0)) ),
% 1.65/0.96      inference(unflattening,[status(thm)],[c_447]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_466,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.65/0.96      | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
% 1.65/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.65/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 1.65/0.96      inference(resolution,[status(thm)],[c_283,c_448]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_358,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,X1,X2)
% 1.65/0.96      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.65/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/0.96      | v2_struct_0(X1)
% 1.65/0.96      | ~ l1_pre_topc(X1)
% 1.65/0.96      | sK0 != X1 ),
% 1.65/0.96      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_359,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.65/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.65/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | v2_struct_0(sK0)
% 1.65/0.96      | ~ l1_pre_topc(sK0) ),
% 1.65/0.96      inference(unflattening,[status(thm)],[c_358]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_363,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.65/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.65/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.65/0.96      inference(global_propositional_subsumption,
% 1.65/0.96                [status(thm)],
% 1.65/0.96                [c_359,c_17,c_15]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_470,plain,
% 1.65/0.96      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.65/0.96      | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
% 1.65/0.96      | ~ m1_connsp_2(X0,sK0,X1)
% 1.65/0.96      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 1.65/0.96      inference(global_propositional_subsumption,[status(thm)],[c_466,c_363]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_471,plain,
% 1.65/0.96      ( ~ m1_connsp_2(X0,sK0,X1)
% 1.65/0.96      | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
% 1.65/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.65/0.96      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 1.65/0.96      inference(renaming,[status(thm)],[c_470]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_910,plain,
% 1.65/0.96      ( m1_connsp_2(X0,sK0,X1) != iProver_top
% 1.65/0.96      | m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1) != iProver_top
% 1.65/0.96      | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
% 1.65/0.96      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,X0),sK2) != iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1355,plain,
% 1.65/0.96      ( m1_connsp_2(X0,sK0,X1) != iProver_top
% 1.65/0.96      | m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1) != iProver_top
% 1.65/0.96      | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) != iProver_top
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,X0),sK2) != iProver_top ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_918,c_910]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1766,plain,
% 1.65/0.96      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X0) != iProver_top
% 1.65/0.96      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
% 1.65/0.96      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),u1_struct_0(sK0)) != iProver_top
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),sK2) != iProver_top ),
% 1.65/0.96      inference(superposition,[status(thm)],[c_1085,c_1355]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1767,plain,
% 1.65/0.96      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X0) != iProver_top
% 1.65/0.96      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
% 1.65/0.96      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 1.65/0.96      inference(light_normalisation,[status(thm)],[c_1766,c_1085]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_22,plain,
% 1.65/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_992,plain,
% 1.65/0.96      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 1.65/0.96      inference(instantiation,[status(thm)],[c_417]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1038,plain,
% 1.65/0.96      ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 1.65/0.96      | k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
% 1.65/0.96      inference(instantiation,[status(thm)],[c_2]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_608,plain,
% 1.65/0.96      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.65/0.96      theory(equality) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1015,plain,
% 1.65/0.96      ( m1_subset_1(X0,X1)
% 1.65/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | X1 != k1_zfmisc_1(u1_struct_0(sK0))
% 1.65/0.96      | X0 != sK2 ),
% 1.65/0.96      inference(instantiation,[status(thm)],[c_608]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1086,plain,
% 1.65/0.96      ( m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),X0)
% 1.65/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | X0 != k1_zfmisc_1(u1_struct_0(sK0))
% 1.65/0.96      | k2_xboole_0(k1_tops_1(sK0,sK2),sK2) != sK2 ),
% 1.65/0.96      inference(instantiation,[status(thm)],[c_1015]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1127,plain,
% 1.65/0.96      ( m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | k2_xboole_0(k1_tops_1(sK0,sK2),sK2) != sK2
% 1.65/0.96      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.65/0.96      inference(instantiation,[status(thm)],[c_1086]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1129,plain,
% 1.65/0.96      ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) != sK2
% 1.65/0.96      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 1.65/0.96      | m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.65/0.96      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_604,plain,( X0 = X0 ),theory(equality) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1128,plain,
% 1.65/0.96      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.65/0.96      inference(instantiation,[status(thm)],[c_604]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1191,plain,
% 1.65/0.96      ( ~ m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.96      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) ),
% 1.65/0.96      inference(instantiation,[status(thm)],[c_4]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1192,plain,
% 1.65/0.96      ( m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.65/0.96      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) = iProver_top ),
% 1.65/0.96      inference(predicate_to_equality,[status(thm)],[c_1191]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1280,plain,
% 1.65/0.96      ( r1_tarski(k1_tops_1(sK0,sK2),X0)
% 1.65/0.96      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),X0) ),
% 1.65/0.96      inference(instantiation,[status(thm)],[c_1]) ).
% 1.65/0.96  
% 1.65/0.96  cnf(c_1486,plain,
% 1.65/0.96      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 1.65/0.96      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1280]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1487,plain,
% 1.65/0.97      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top
% 1.65/0.97      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) != iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1230,plain,
% 1.65/0.97      ( m1_connsp_2(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),sK0,sK1) != iProver_top
% 1.65/0.97      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X0) != iProver_top
% 1.65/0.97      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 1.65/0.97      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.65/0.97      | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),sK2) != iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1085,c_910]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1231,plain,
% 1.65/0.97      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,X0) != iProver_top
% 1.65/0.97      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
% 1.65/0.97      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 1.65/0.97      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.65/0.97      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 1.65/0.97      inference(light_normalisation,[status(thm)],[c_1230,c_1085]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_14,negated_conjecture,
% 1.65/0.97      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.65/0.97      inference(cnf_transformation,[],[f47]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_21,plain,
% 1.65/0.97      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_12,negated_conjecture,
% 1.65/0.97      ( m1_connsp_2(sK2,sK0,sK1) ),
% 1.65/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_23,plain,
% 1.65/0.97      ( m1_connsp_2(sK2,sK0,sK1) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_993,plain,
% 1.65/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.65/0.97      | r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1003,plain,
% 1.65/0.97      ( ~ m1_connsp_2(X0,sK0,sK1)
% 1.65/0.97      | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
% 1.65/0.97      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.97      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.65/0.97      | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_471]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1058,plain,
% 1.65/0.97      ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 1.65/0.97      | ~ m1_connsp_2(sK2,sK0,sK1)
% 1.65/0.97      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.65/0.97      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.65/0.97      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 1.65/0.97      inference(instantiation,[status(thm)],[c_1003]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1059,plain,
% 1.65/0.97      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
% 1.65/0.97      | m1_connsp_2(sK2,sK0,sK1) != iProver_top
% 1.65/0.97      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.65/0.97      | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
% 1.65/0.97      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_1058]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1672,plain,
% 1.65/0.97      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.65/0.97      | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top ),
% 1.65/0.97      inference(global_propositional_subsumption,
% 1.65/0.97                [status(thm)],
% 1.65/0.97                [c_1231,c_21,c_22,c_23,c_993,c_1059]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1673,plain,
% 1.65/0.97      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
% 1.65/0.97      | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.65/0.97      inference(renaming,[status(thm)],[c_1672]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1678,plain,
% 1.65/0.97      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top
% 1.65/0.97      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_918,c_1673]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_2107,plain,
% 1.65/0.97      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) != iProver_top ),
% 1.65/0.97      inference(global_propositional_subsumption,
% 1.65/0.97                [status(thm)],
% 1.65/0.97                [c_1767,c_13,c_22,c_992,c_1038,c_1129,c_1128,c_1192,c_1487,
% 1.65/0.97                 c_1678]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1354,plain,
% 1.65/0.97      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 1.65/0.97      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_918,c_912]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1563,plain,
% 1.65/0.97      ( k2_xboole_0(k1_tops_1(sK0,X0),X0) = X0
% 1.65/0.97      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1354,c_919]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1992,plain,
% 1.65/0.97      ( k2_xboole_0(k1_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0))),k1_tops_1(sK0,u1_struct_0(sK0))) = k1_tops_1(sK0,u1_struct_0(sK0))
% 1.65/0.97      | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1354,c_1563]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1562,plain,
% 1.65/0.97      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = iProver_top
% 1.65/0.97      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1085,c_1354]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1665,plain,
% 1.65/0.97      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = iProver_top ),
% 1.65/0.97      inference(global_propositional_subsumption,
% 1.65/0.97                [status(thm)],
% 1.65/0.97                [c_1562,c_13,c_22,c_992,c_1038,c_1129,c_1128,c_1192,c_1487]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1670,plain,
% 1.65/0.97      ( k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1665,c_919]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1353,plain,
% 1.65/0.97      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 1.65/0.97      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_918,c_911]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1580,plain,
% 1.65/0.97      ( k1_tops_1(sK0,k1_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0)))) = k1_tops_1(sK0,k1_tops_1(sK0,u1_struct_0(sK0)))
% 1.65/0.97      | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1354,c_1353]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1452,plain,
% 1.65/0.97      ( k2_xboole_0(sK2,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1347,c_919]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_1509,plain,
% 1.65/0.97      ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 1.65/0.97      | r1_tarski(sK2,X0) = iProver_top ),
% 1.65/0.97      inference(superposition,[status(thm)],[c_1452,c_920]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_913,plain,
% 1.65/0.97      ( m1_connsp_2(X0,sK0,X1) != iProver_top
% 1.65/0.97      | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
% 1.65/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_916,plain,
% 1.65/0.97      ( m1_connsp_2(sK2,sK0,sK1) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.65/0.97  
% 1.65/0.97  cnf(c_914,plain,
% 1.65/0.97      ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.65/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  % SZS output end Saturation for theBenchmark.p
% 1.65/0.97  
% 1.65/0.97  ------                               Statistics
% 1.65/0.97  
% 1.65/0.97  ------ General
% 1.65/0.97  
% 1.65/0.97  abstr_ref_over_cycles:                  0
% 1.65/0.97  abstr_ref_under_cycles:                 0
% 1.65/0.97  gc_basic_clause_elim:                   0
% 1.65/0.97  forced_gc_time:                         0
% 1.65/0.97  parsing_time:                           0.008
% 1.65/0.97  unif_index_cands_time:                  0.
% 1.65/0.97  unif_index_add_time:                    0.
% 1.65/0.97  orderings_time:                         0.
% 1.65/0.97  out_proof_time:                         0.
% 1.65/0.97  total_time:                             0.105
% 1.65/0.97  num_of_symbols:                         47
% 1.65/0.97  num_of_terms:                           1630
% 1.65/0.97  
% 1.65/0.97  ------ Preprocessing
% 1.65/0.97  
% 1.65/0.97  num_of_splits:                          0
% 1.65/0.97  num_of_split_atoms:                     0
% 1.65/0.97  num_of_reused_defs:                     0
% 1.65/0.97  num_eq_ax_congr_red:                    9
% 1.65/0.97  num_of_sem_filtered_clauses:            1
% 1.65/0.97  num_of_subtypes:                        0
% 1.65/0.97  monotx_restored_types:                  0
% 1.65/0.97  sat_num_of_epr_types:                   0
% 1.65/0.97  sat_num_of_non_cyclic_types:            0
% 1.65/0.97  sat_guarded_non_collapsed_types:        0
% 1.65/0.97  num_pure_diseq_elim:                    0
% 1.65/0.97  simp_replaced_by:                       0
% 1.65/0.97  res_preprocessed:                       68
% 1.65/0.97  prep_upred:                             0
% 1.65/0.97  prep_unflattend:                        11
% 1.65/0.97  smt_new_axioms:                         0
% 1.65/0.97  pred_elim_cands:                        3
% 1.65/0.97  pred_elim:                              6
% 1.65/0.97  pred_elim_cl:                           7
% 1.65/0.97  pred_elim_cycles:                       10
% 1.65/0.97  merged_defs:                            8
% 1.65/0.97  merged_defs_ncl:                        0
% 1.65/0.97  bin_hyper_res:                          8
% 1.65/0.97  prep_cycles:                            4
% 1.65/0.97  pred_elim_time:                         0.005
% 1.65/0.97  splitting_time:                         0.
% 1.65/0.97  sem_filter_time:                        0.
% 1.65/0.97  monotx_time:                            0.
% 1.65/0.97  subtype_inf_time:                       0.
% 1.65/0.97  
% 1.65/0.97  ------ Problem properties
% 1.65/0.97  
% 1.65/0.97  clauses:                                11
% 1.65/0.97  conjectures:                            3
% 1.65/0.97  epr:                                    1
% 1.65/0.97  horn:                                   11
% 1.65/0.97  ground:                                 3
% 1.65/0.97  unary:                                  3
% 1.65/0.97  binary:                                 6
% 1.65/0.97  lits:                                   23
% 1.65/0.97  lits_eq:                                2
% 1.65/0.97  fd_pure:                                0
% 1.65/0.97  fd_pseudo:                              0
% 1.65/0.97  fd_cond:                                0
% 1.65/0.97  fd_pseudo_cond:                         0
% 1.65/0.97  ac_symbols:                             0
% 1.65/0.97  
% 1.65/0.97  ------ Propositional Solver
% 1.65/0.97  
% 1.65/0.97  prop_solver_calls:                      27
% 1.65/0.97  prop_fast_solver_calls:                 480
% 1.65/0.97  smt_solver_calls:                       0
% 1.65/0.97  smt_fast_solver_calls:                  0
% 1.65/0.97  prop_num_of_clauses:                    869
% 1.65/0.97  prop_preprocess_simplified:             2948
% 1.65/0.97  prop_fo_subsumed:                       18
% 1.65/0.97  prop_solver_time:                       0.
% 1.65/0.97  smt_solver_time:                        0.
% 1.65/0.97  smt_fast_solver_time:                   0.
% 1.65/0.97  prop_fast_solver_time:                  0.
% 1.65/0.97  prop_unsat_core_time:                   0.
% 1.65/0.97  
% 1.65/0.97  ------ QBF
% 1.65/0.97  
% 1.65/0.97  qbf_q_res:                              0
% 1.65/0.97  qbf_num_tautologies:                    0
% 1.65/0.97  qbf_prep_cycles:                        0
% 1.65/0.97  
% 1.65/0.97  ------ BMC1
% 1.65/0.97  
% 1.65/0.97  bmc1_current_bound:                     -1
% 1.65/0.97  bmc1_last_solved_bound:                 -1
% 1.65/0.97  bmc1_unsat_core_size:                   -1
% 1.65/0.97  bmc1_unsat_core_parents_size:           -1
% 1.65/0.97  bmc1_merge_next_fun:                    0
% 1.65/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.65/0.97  
% 1.65/0.97  ------ Instantiation
% 1.65/0.97  
% 1.65/0.97  inst_num_of_clauses:                    290
% 1.65/0.97  inst_num_in_passive:                    5
% 1.65/0.97  inst_num_in_active:                     161
% 1.65/0.97  inst_num_in_unprocessed:                124
% 1.65/0.97  inst_num_of_loops:                      170
% 1.65/0.97  inst_num_of_learning_restarts:          0
% 1.65/0.97  inst_num_moves_active_passive:          5
% 1.65/0.97  inst_lit_activity:                      0
% 1.65/0.97  inst_lit_activity_moves:                0
% 1.65/0.97  inst_num_tautologies:                   0
% 1.65/0.97  inst_num_prop_implied:                  0
% 1.65/0.97  inst_num_existing_simplified:           0
% 1.65/0.97  inst_num_eq_res_simplified:             0
% 1.65/0.97  inst_num_child_elim:                    0
% 1.65/0.97  inst_num_of_dismatching_blockings:      47
% 1.65/0.97  inst_num_of_non_proper_insts:           277
% 1.65/0.97  inst_num_of_duplicates:                 0
% 1.65/0.97  inst_inst_num_from_inst_to_res:         0
% 1.65/0.97  inst_dismatching_checking_time:         0.
% 1.65/0.97  
% 1.65/0.97  ------ Resolution
% 1.65/0.97  
% 1.65/0.97  res_num_of_clauses:                     0
% 1.65/0.97  res_num_in_passive:                     0
% 1.65/0.97  res_num_in_active:                      0
% 1.65/0.97  res_num_of_loops:                       72
% 1.65/0.97  res_forward_subset_subsumed:            37
% 1.65/0.97  res_backward_subset_subsumed:           0
% 1.65/0.97  res_forward_subsumed:                   0
% 1.65/0.97  res_backward_subsumed:                  0
% 1.65/0.97  res_forward_subsumption_resolution:     0
% 1.65/0.97  res_backward_subsumption_resolution:    0
% 1.65/0.97  res_clause_to_clause_subsumption:       87
% 1.65/0.97  res_orphan_elimination:                 0
% 1.65/0.97  res_tautology_del:                      56
% 1.65/0.97  res_num_eq_res_simplified:              0
% 1.65/0.97  res_num_sel_changes:                    0
% 1.65/0.97  res_moves_from_active_to_pass:          0
% 1.65/0.97  
% 1.65/0.97  ------ Superposition
% 1.65/0.97  
% 1.65/0.97  sup_time_total:                         0.
% 1.65/0.97  sup_time_generating:                    0.
% 1.65/0.97  sup_time_sim_full:                      0.
% 1.65/0.97  sup_time_sim_immed:                     0.
% 1.65/0.97  
% 1.65/0.97  sup_num_of_clauses:                     32
% 1.65/0.97  sup_num_in_active:                      31
% 1.65/0.97  sup_num_in_passive:                     1
% 1.65/0.97  sup_num_of_loops:                       32
% 1.65/0.97  sup_fw_superposition:                   15
% 1.65/0.97  sup_bw_superposition:                   16
% 1.65/0.97  sup_immediate_simplified:               7
% 1.65/0.97  sup_given_eliminated:                   0
% 1.65/0.97  comparisons_done:                       0
% 1.65/0.97  comparisons_avoided:                    0
% 1.65/0.97  
% 1.65/0.97  ------ Simplifications
% 1.65/0.97  
% 1.65/0.97  
% 1.65/0.97  sim_fw_subset_subsumed:                 1
% 1.65/0.97  sim_bw_subset_subsumed:                 2
% 1.65/0.97  sim_fw_subsumed:                        0
% 1.65/0.97  sim_bw_subsumed:                        0
% 1.65/0.97  sim_fw_subsumption_res:                 0
% 1.65/0.97  sim_bw_subsumption_res:                 0
% 1.65/0.97  sim_tautology_del:                      2
% 1.65/0.97  sim_eq_tautology_del:                   4
% 1.65/0.97  sim_eq_res_simp:                        0
% 1.65/0.97  sim_fw_demodulated:                     0
% 1.65/0.97  sim_bw_demodulated:                     0
% 1.65/0.97  sim_light_normalised:                   6
% 1.65/0.97  sim_joinable_taut:                      0
% 1.65/0.97  sim_joinable_simp:                      0
% 1.65/0.97  sim_ac_normalised:                      0
% 1.65/0.97  sim_smt_subsumption:                    0
% 1.65/0.97  
%------------------------------------------------------------------------------

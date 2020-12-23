%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:17 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 166 expanded)
%              Number of clauses        :   52 (  56 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  458 (1232 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   4 average)
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

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f41,plain,(
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

fof(f49,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_233,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | ~ v1_xboole_0(X1_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1669,plain,
    ( ~ r2_hidden(X0_43,k1_tops_1(sK0,sK2))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_1671,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_6,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_227,plain,
    ( v3_pre_topc(X0_43,X0_44)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(X1_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X1_44)
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,X0_43) != X0_43 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_235,plain,
    ( v3_pre_topc(X0_43,X0_44)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,X0_43) != X0_43
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_227])).

cnf(c_236,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_227])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_227])).

cnf(c_474,plain,
    ( k1_tops_1(X0_44,X0_43) != X0_43
    | ~ l1_pre_topc(X0_44)
    | ~ v2_pre_topc(X0_44)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | v3_pre_topc(X0_43,X0_44) ),
    inference(global_propositional_subsumption,[status(thm)],[c_235,c_236,c_234])).

cnf(c_475,plain,
    ( v3_pre_topc(X0_43,X0_44)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,X0_43) != X0_43 ),
    inference(renaming,[status(thm)],[c_474])).

cnf(c_1027,plain,
    ( v3_pre_topc(k1_tops_1(X0_44,X0_43),X0_44)
    | ~ m1_subset_1(k1_tops_1(X0_44,X0_43),k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,k1_tops_1(X0_44,X0_43)) != k1_tops_1(X0_44,X0_43) ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_1653,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_225,plain,
    ( m1_connsp_2(X0_43,X0_44,X1_43)
    | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
    | v2_struct_0(X0_44)
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1576,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_243,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | r2_hidden(X0_43,X2_43)
    | X2_43 != X1_43 ),
    theory(equality)).

cnf(c_1090,plain,
    ( r2_hidden(sK1,X0_43)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | X0_43 != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_1187,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,X0_43))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,X0_43) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_1359,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_1187])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_231,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1332,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_232,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X0_43)
    | r1_tarski(X2_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1083,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0_43)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,X0_43) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_1181,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_11,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_223,negated_conjecture,
    ( ~ m1_connsp_2(X0_43,sK0,sK1)
    | ~ v3_pre_topc(X0_43,sK0)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_43,sK2)
    | v1_xboole_0(X0_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1072,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_188,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_10])).

cnf(c_189,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_216,plain,
    ( ~ m1_connsp_2(X0_43,X0_44,X1_43)
    | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
    | r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
    | v2_struct_0(X0_44)
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_189])).

cnf(c_1023,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,k1_tops_1(X0_44,X0_43)) = k1_tops_1(X0_44,X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_974,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | r1_tarski(k1_tops_1(X0_44,X0_43),X0_43)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_971,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_952,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_12,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1671,c_1653,c_1576,c_1359,c_1332,c_1181,c_1072,c_1023,c_974,c_971,c_952,c_12,c_13,c_14,c_15,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.04/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.00  
% 3.04/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/1.00  
% 3.04/1.00  ------  iProver source info
% 3.04/1.00  
% 3.04/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.04/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/1.00  git: non_committed_changes: false
% 3.04/1.00  git: last_make_outside_of_git: false
% 3.04/1.00  
% 3.04/1.00  ------ 
% 3.04/1.00  ------ Parsing...
% 3.04/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/1.00  
% 3.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.04/1.00  
% 3.04/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/1.00  
% 3.04/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/1.00  ------ Proving...
% 3.04/1.00  ------ Problem Properties 
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  clauses                                 22
% 3.04/1.00  conjectures                             7
% 3.04/1.00  EPR                                     8
% 3.04/1.00  Horn                                    17
% 3.04/1.00  unary                                   6
% 3.04/1.00  binary                                  5
% 3.04/1.00  lits                                    67
% 3.04/1.00  lits eq                                 3
% 3.04/1.00  fd_pure                                 0
% 3.04/1.00  fd_pseudo                               0
% 3.04/1.00  fd_cond                                 0
% 3.04/1.00  fd_pseudo_cond                          0
% 3.04/1.00  AC symbols                              0
% 3.04/1.00  
% 3.04/1.00  ------ Input Options Time Limit: Unbounded
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  ------ 
% 3.04/1.00  Current options:
% 3.04/1.00  ------ 
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  ------ Proving...
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  % SZS status Theorem for theBenchmark.p
% 3.04/1.00  
% 3.04/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/1.00  
% 3.04/1.00  fof(f1,axiom,(
% 3.04/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f11,plain,(
% 3.04/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.04/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.04/1.00  
% 3.04/1.00  fof(f12,plain,(
% 3.04/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.04/1.00    inference(ennf_transformation,[],[f11])).
% 3.04/1.00  
% 3.04/1.00  fof(f32,plain,(
% 3.04/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f12])).
% 3.04/1.00  
% 3.04/1.00  fof(f6,axiom,(
% 3.04/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f18,plain,(
% 3.04/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.04/1.00    inference(ennf_transformation,[],[f6])).
% 3.04/1.00  
% 3.04/1.00  fof(f19,plain,(
% 3.04/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.04/1.00    inference(flattening,[],[f18])).
% 3.04/1.00  
% 3.04/1.00  fof(f39,plain,(
% 3.04/1.00    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f19])).
% 3.04/1.00  
% 3.04/1.00  fof(f7,axiom,(
% 3.04/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f20,plain,(
% 3.04/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/1.00    inference(ennf_transformation,[],[f7])).
% 3.04/1.00  
% 3.04/1.00  fof(f21,plain,(
% 3.04/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/1.00    inference(flattening,[],[f20])).
% 3.04/1.00  
% 3.04/1.00  fof(f27,plain,(
% 3.04/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/1.00    inference(nnf_transformation,[],[f21])).
% 3.04/1.00  
% 3.04/1.00  fof(f41,plain,(
% 3.04/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f27])).
% 3.04/1.00  
% 3.04/1.00  fof(f3,axiom,(
% 3.04/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f26,plain,(
% 3.04/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.04/1.00    inference(nnf_transformation,[],[f3])).
% 3.04/1.00  
% 3.04/1.00  fof(f35,plain,(
% 3.04/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f26])).
% 3.04/1.00  
% 3.04/1.00  fof(f2,axiom,(
% 3.04/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f13,plain,(
% 3.04/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.04/1.00    inference(ennf_transformation,[],[f2])).
% 3.04/1.00  
% 3.04/1.00  fof(f14,plain,(
% 3.04/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.04/1.00    inference(flattening,[],[f13])).
% 3.04/1.00  
% 3.04/1.00  fof(f33,plain,(
% 3.04/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f14])).
% 3.04/1.00  
% 3.04/1.00  fof(f9,conjecture,(
% 3.04/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 3.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f10,negated_conjecture,(
% 3.04/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 3.04/1.00    inference(negated_conjecture,[],[f9])).
% 3.04/1.00  
% 3.04/1.00  fof(f24,plain,(
% 3.04/1.00    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.04/1.00    inference(ennf_transformation,[],[f10])).
% 3.04/1.00  
% 3.04/1.00  fof(f25,plain,(
% 3.04/1.00    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.04/1.00    inference(flattening,[],[f24])).
% 3.04/1.00  
% 3.04/1.00  fof(f30,plain,(
% 3.04/1.00    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.04/1.00    introduced(choice_axiom,[])).
% 3.04/1.00  
% 3.04/1.00  fof(f29,plain,(
% 3.04/1.00    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 3.04/1.00    introduced(choice_axiom,[])).
% 3.04/1.00  
% 3.04/1.00  fof(f28,plain,(
% 3.04/1.00    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.04/1.00    introduced(choice_axiom,[])).
% 3.04/1.00  
% 3.04/1.00  fof(f31,plain,(
% 3.04/1.00    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30,f29,f28])).
% 3.04/1.00  
% 3.04/1.00  fof(f49,plain,(
% 3.04/1.00    ( ! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f31])).
% 3.04/1.00  
% 3.04/1.00  fof(f40,plain,(
% 3.04/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f27])).
% 3.04/1.00  
% 3.04/1.00  fof(f8,axiom,(
% 3.04/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f22,plain,(
% 3.04/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/1.00    inference(ennf_transformation,[],[f8])).
% 3.04/1.00  
% 3.04/1.00  fof(f23,plain,(
% 3.04/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/1.00    inference(flattening,[],[f22])).
% 3.04/1.00  
% 3.04/1.00  fof(f42,plain,(
% 3.04/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f23])).
% 3.04/1.00  
% 3.04/1.00  fof(f4,axiom,(
% 3.04/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 3.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f15,plain,(
% 3.04/1.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.04/1.00    inference(ennf_transformation,[],[f4])).
% 3.04/1.00  
% 3.04/1.00  fof(f16,plain,(
% 3.04/1.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.04/1.00    inference(flattening,[],[f15])).
% 3.04/1.00  
% 3.04/1.00  fof(f36,plain,(
% 3.04/1.00    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f16])).
% 3.04/1.00  
% 3.04/1.00  fof(f5,axiom,(
% 3.04/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f17,plain,(
% 3.04/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.04/1.00    inference(ennf_transformation,[],[f5])).
% 3.04/1.00  
% 3.04/1.00  fof(f37,plain,(
% 3.04/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f17])).
% 3.04/1.00  
% 3.04/1.00  fof(f34,plain,(
% 3.04/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.04/1.00    inference(cnf_transformation,[],[f26])).
% 3.04/1.00  
% 3.04/1.00  fof(f48,plain,(
% 3.04/1.00    m1_connsp_2(sK2,sK0,sK1)),
% 3.04/1.00    inference(cnf_transformation,[],[f31])).
% 3.04/1.00  
% 3.04/1.00  fof(f47,plain,(
% 3.04/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.04/1.00    inference(cnf_transformation,[],[f31])).
% 3.04/1.00  
% 3.04/1.00  fof(f46,plain,(
% 3.04/1.00    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.04/1.00    inference(cnf_transformation,[],[f31])).
% 3.04/1.00  
% 3.04/1.00  fof(f45,plain,(
% 3.04/1.00    l1_pre_topc(sK0)),
% 3.04/1.00    inference(cnf_transformation,[],[f31])).
% 3.04/1.00  
% 3.04/1.00  fof(f44,plain,(
% 3.04/1.00    v2_pre_topc(sK0)),
% 3.04/1.00    inference(cnf_transformation,[],[f31])).
% 3.04/1.00  
% 3.04/1.00  fof(f43,plain,(
% 3.04/1.00    ~v2_struct_0(sK0)),
% 3.04/1.00    inference(cnf_transformation,[],[f31])).
% 3.04/1.00  
% 3.04/1.00  cnf(c_0,plain,
% 3.04/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.04/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_233,plain,
% 3.04/1.00      ( ~ r2_hidden(X0_43,X1_43) | ~ v1_xboole_0(X1_43) ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1669,plain,
% 3.04/1.00      ( ~ r2_hidden(X0_43,k1_tops_1(sK0,sK2))
% 3.04/1.00      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_233]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1671,plain,
% 3.04/1.00      ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.04/1.00      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_1669]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_6,plain,
% 3.04/1.00      ( v3_pre_topc(X0,X1)
% 3.04/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/1.00      | ~ v2_pre_topc(X1)
% 3.04/1.00      | ~ l1_pre_topc(X1)
% 3.04/1.00      | ~ l1_pre_topc(X3)
% 3.04/1.00      | k1_tops_1(X1,X0) != X0 ),
% 3.04/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_227,plain,
% 3.04/1.00      ( v3_pre_topc(X0_43,X0_44)
% 3.04/1.00      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.04/1.00      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(X1_44)))
% 3.04/1.00      | ~ v2_pre_topc(X0_44)
% 3.04/1.00      | ~ l1_pre_topc(X1_44)
% 3.04/1.00      | ~ l1_pre_topc(X0_44)
% 3.04/1.00      | k1_tops_1(X0_44,X0_43) != X0_43 ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_235,plain,
% 3.04/1.00      ( v3_pre_topc(X0_43,X0_44)
% 3.04/1.00      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.04/1.00      | ~ v2_pre_topc(X0_44)
% 3.04/1.00      | ~ l1_pre_topc(X0_44)
% 3.04/1.00      | k1_tops_1(X0_44,X0_43) != X0_43
% 3.04/1.00      | ~ sP1_iProver_split ),
% 3.04/1.00      inference(splitting,
% 3.04/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.04/1.00                [c_227]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_236,plain,
% 3.04/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 3.04/1.00      inference(splitting,
% 3.04/1.00                [splitting(split),new_symbols(definition,[])],
% 3.04/1.00                [c_227]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_234,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.04/1.00      | ~ l1_pre_topc(X0_44)
% 3.04/1.00      | ~ sP0_iProver_split ),
% 3.04/1.00      inference(splitting,
% 3.04/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.04/1.00                [c_227]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_474,plain,
% 3.04/1.00      ( k1_tops_1(X0_44,X0_43) != X0_43
% 3.04/1.00      | ~ l1_pre_topc(X0_44)
% 3.04/1.00      | ~ v2_pre_topc(X0_44)
% 3.04/1.00      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.04/1.00      | v3_pre_topc(X0_43,X0_44) ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_235,c_236,c_234]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_475,plain,
% 3.04/1.00      ( v3_pre_topc(X0_43,X0_44)
% 3.04/1.00      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.04/1.00      | ~ v2_pre_topc(X0_44)
% 3.04/1.00      | ~ l1_pre_topc(X0_44)
% 3.04/1.00      | k1_tops_1(X0_44,X0_43) != X0_43 ),
% 3.04/1.00      inference(renaming,[status(thm)],[c_474]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1027,plain,
% 3.04/1.00      ( v3_pre_topc(k1_tops_1(X0_44,X0_43),X0_44)
% 3.04/1.00      | ~ m1_subset_1(k1_tops_1(X0_44,X0_43),k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.04/1.00      | ~ v2_pre_topc(X0_44)
% 3.04/1.00      | ~ l1_pre_topc(X0_44)
% 3.04/1.00      | k1_tops_1(X0_44,k1_tops_1(X0_44,X0_43)) != k1_tops_1(X0_44,X0_43) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_475]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1653,plain,
% 3.04/1.00      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 3.04/1.00      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.04/1.00      | ~ v2_pre_topc(sK0)
% 3.04/1.00      | ~ l1_pre_topc(sK0)
% 3.04/1.00      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_1027]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_8,plain,
% 3.04/1.00      ( m1_connsp_2(X0,X1,X2)
% 3.04/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/1.00      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.04/1.00      | v2_struct_0(X1)
% 3.04/1.00      | ~ v2_pre_topc(X1)
% 3.04/1.00      | ~ l1_pre_topc(X1) ),
% 3.04/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_225,plain,
% 3.04/1.00      ( m1_connsp_2(X0_43,X0_44,X1_43)
% 3.04/1.00      | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
% 3.04/1.00      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.04/1.00      | ~ r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
% 3.04/1.00      | v2_struct_0(X0_44)
% 3.04/1.00      | ~ v2_pre_topc(X0_44)
% 3.04/1.00      | ~ l1_pre_topc(X0_44) ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1576,plain,
% 3.04/1.00      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 3.04/1.00      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.04/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 3.04/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 3.04/1.00      | v2_struct_0(sK0)
% 3.04/1.00      | ~ v2_pre_topc(sK0)
% 3.04/1.00      | ~ l1_pre_topc(sK0) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_225]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_243,plain,
% 3.04/1.00      ( ~ r2_hidden(X0_43,X1_43)
% 3.04/1.00      | r2_hidden(X0_43,X2_43)
% 3.04/1.00      | X2_43 != X1_43 ),
% 3.04/1.00      theory(equality) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1090,plain,
% 3.04/1.00      ( r2_hidden(sK1,X0_43)
% 3.04/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.04/1.00      | X0_43 != k1_tops_1(sK0,sK2) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_243]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1187,plain,
% 3.04/1.00      ( r2_hidden(sK1,k1_tops_1(sK0,X0_43))
% 3.04/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.04/1.00      | k1_tops_1(sK0,X0_43) != k1_tops_1(sK0,sK2) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_1090]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1359,plain,
% 3.04/1.00      ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 3.04/1.00      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.04/1.00      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_1187]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2,plain,
% 3.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.04/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_231,plain,
% 3.04/1.00      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.04/1.00      | ~ r1_tarski(X0_43,X1_43) ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1332,plain,
% 3.04/1.00      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.04/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_231]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1,plain,
% 3.04/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.04/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_232,plain,
% 3.04/1.00      ( ~ r1_tarski(X0_43,X1_43)
% 3.04/1.00      | ~ r1_tarski(X2_43,X0_43)
% 3.04/1.00      | r1_tarski(X2_43,X1_43) ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1083,plain,
% 3.04/1.00      ( r1_tarski(k1_tops_1(sK0,sK2),X0_43)
% 3.04/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.04/1.00      | ~ r1_tarski(sK2,X0_43) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_232]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1181,plain,
% 3.04/1.00      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 3.04/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.04/1.00      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_1083]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11,negated_conjecture,
% 3.04/1.00      ( ~ m1_connsp_2(X0,sK0,sK1)
% 3.04/1.00      | ~ v3_pre_topc(X0,sK0)
% 3.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.04/1.00      | ~ r1_tarski(X0,sK2)
% 3.04/1.00      | v1_xboole_0(X0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_223,negated_conjecture,
% 3.04/1.00      ( ~ m1_connsp_2(X0_43,sK0,sK1)
% 3.04/1.00      | ~ v3_pre_topc(X0_43,sK0)
% 3.04/1.00      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.04/1.00      | ~ r1_tarski(X0_43,sK2)
% 3.04/1.00      | v1_xboole_0(X0_43) ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1072,plain,
% 3.04/1.00      ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 3.04/1.00      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 3.04/1.00      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.04/1.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.04/1.00      | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_223]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_9,plain,
% 3.04/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.04/1.00      | v2_struct_0(X1)
% 3.04/1.00      | ~ v2_pre_topc(X1)
% 3.04/1.00      | ~ l1_pre_topc(X1) ),
% 3.04/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_10,plain,
% 3.04/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/1.00      | v2_struct_0(X1)
% 3.04/1.00      | ~ v2_pre_topc(X1)
% 3.04/1.00      | ~ l1_pre_topc(X1) ),
% 3.04/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_188,plain,
% 3.04/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 3.04/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.04/1.00      | v2_struct_0(X1)
% 3.04/1.00      | ~ v2_pre_topc(X1)
% 3.04/1.00      | ~ l1_pre_topc(X1) ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_9,c_10]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_189,plain,
% 3.04/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/1.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.04/1.00      | v2_struct_0(X1)
% 3.04/1.00      | ~ v2_pre_topc(X1)
% 3.04/1.00      | ~ l1_pre_topc(X1) ),
% 3.04/1.00      inference(renaming,[status(thm)],[c_188]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_216,plain,
% 3.04/1.00      ( ~ m1_connsp_2(X0_43,X0_44,X1_43)
% 3.04/1.00      | ~ m1_subset_1(X1_43,u1_struct_0(X0_44))
% 3.04/1.00      | r2_hidden(X1_43,k1_tops_1(X0_44,X0_43))
% 3.04/1.00      | v2_struct_0(X0_44)
% 3.04/1.00      | ~ v2_pre_topc(X0_44)
% 3.04/1.00      | ~ l1_pre_topc(X0_44) ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_189]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1023,plain,
% 3.04/1.00      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 3.04/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 3.04/1.00      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 3.04/1.00      | v2_struct_0(sK0)
% 3.04/1.00      | ~ v2_pre_topc(sK0)
% 3.04/1.00      | ~ l1_pre_topc(sK0) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_216]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_4,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/1.00      | ~ l1_pre_topc(X1)
% 3.04/1.00      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_229,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.04/1.00      | ~ l1_pre_topc(X0_44)
% 3.04/1.00      | k1_tops_1(X0_44,k1_tops_1(X0_44,X0_43)) = k1_tops_1(X0_44,X0_43) ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_974,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.04/1.00      | ~ l1_pre_topc(sK0)
% 3.04/1.00      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_229]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_5,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.04/1.00      | ~ l1_pre_topc(X1) ),
% 3.04/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_228,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.04/1.00      | r1_tarski(k1_tops_1(X0_44,X0_43),X0_43)
% 3.04/1.00      | ~ l1_pre_topc(X0_44) ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_971,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.04/1.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 3.04/1.00      | ~ l1_pre_topc(sK0) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_228]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_3,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.04/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_230,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.04/1.00      | r1_tarski(X0_43,X1_43) ),
% 3.04/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_952,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.04/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_230]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_12,negated_conjecture,
% 3.04/1.00      ( m1_connsp_2(sK2,sK0,sK1) ),
% 3.04/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_13,negated_conjecture,
% 3.04/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.04/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_14,negated_conjecture,
% 3.04/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 3.04/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_15,negated_conjecture,
% 3.04/1.00      ( l1_pre_topc(sK0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_16,negated_conjecture,
% 3.04/1.00      ( v2_pre_topc(sK0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_17,negated_conjecture,
% 3.04/1.00      ( ~ v2_struct_0(sK0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(contradiction,plain,
% 3.04/1.00      ( $false ),
% 3.04/1.00      inference(minisat,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_1671,c_1653,c_1576,c_1359,c_1332,c_1181,c_1072,c_1023,
% 3.04/1.00                 c_974,c_971,c_952,c_12,c_13,c_14,c_15,c_16,c_17]) ).
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/1.00  
% 3.04/1.00  ------                               Statistics
% 3.04/1.00  
% 3.04/1.00  ------ Selected
% 3.04/1.00  
% 3.04/1.00  total_time:                             0.099
% 3.04/1.00  
%------------------------------------------------------------------------------

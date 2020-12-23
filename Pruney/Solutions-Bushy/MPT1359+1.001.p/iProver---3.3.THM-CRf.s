%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1359+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:33 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  243 (29573 expanded)
%              Number of clauses        :  176 (6177 expanded)
%              Number of leaves         :   15 (6805 expanded)
%              Depth                    :   38
%              Number of atoms          : 1050 (250373 expanded)
%              Number of equality atoms :  470 (61059 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
              & v1_finset_1(X2)
              & r1_tarski(X2,X1)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
          | ~ v2_tops_2(X1,X0)
          | k1_xboole_0 = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
                | ~ v1_finset_1(X2)
                | ~ r1_tarski(X2,X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
            & v2_tops_2(X1,X0)
            & k1_xboole_0 != X1
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                & v1_finset_1(X2)
                & r1_tarski(X2,X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | k1_xboole_0 = X1
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
                | ~ v1_finset_1(X2)
                | ~ r1_tarski(X2,X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
            & v2_tops_2(X1,X0)
            & k1_xboole_0 != X1
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X3] :
            ( ? [X4] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X4)
                & v1_finset_1(X4)
                & r1_tarski(X4,X3)
                & k1_xboole_0 != X4
                & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X3)
            | ~ v2_tops_2(X3,X0)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f31,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X4)
          & v1_finset_1(X4)
          & r1_tarski(X4,X3)
          & k1_xboole_0 != X4
          & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK4(X0,X3))
        & v1_finset_1(sK4(X0,X3))
        & r1_tarski(sK4(X0,X3),X3)
        & k1_xboole_0 != sK4(X0,X3)
        & m1_subset_1(sK4(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
              | ~ v1_finset_1(X2)
              | ~ r1_tarski(X2,X1)
              | k1_xboole_0 = X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
          & v2_tops_2(X1,X0)
          & k1_xboole_0 != X1
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X2] :
            ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
            | ~ v1_finset_1(X2)
            | ~ r1_tarski(X2,sK3(X0))
            | k1_xboole_0 = X2
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK3(X0))
        & v2_tops_2(sK3(X0),X0)
        & k1_xboole_0 != sK3(X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X2] :
              ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
              | ~ v1_finset_1(X2)
              | ~ r1_tarski(X2,sK3(X0))
              | k1_xboole_0 = X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK3(X0))
          & v2_tops_2(sK3(X0),X0)
          & k1_xboole_0 != sK3(X0)
          & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X3] :
            ( ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK4(X0,X3))
              & v1_finset_1(sK4(X0,X3))
              & r1_tarski(sK4(X0,X3),X3)
              & k1_xboole_0 != sK4(X0,X3)
              & m1_subset_1(sK4(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X3)
            | ~ v2_tops_2(X3,X0)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f31,f30])).

fof(f54,plain,(
    ! [X0,X3] :
      ( r1_tarski(sK4(X0,X3),X3)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X3)
      | ~ v2_tops_2(X3,X0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
                & v2_tops_2(X1,X0)
                & v3_finset_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | ~ v3_finset_1(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | ~ v3_finset_1(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
              & v2_tops_2(X1,X0)
              & v3_finset_1(X1)
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X1] :
              ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
              | ~ v2_tops_2(X1,X0)
              | ~ v3_finset_1(X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
              & v2_tops_2(X1,X0)
              & v3_finset_1(X1)
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X2] :
              ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
              | ~ v2_tops_2(X2,X0)
              | ~ v3_finset_1(X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
          & v2_tops_2(X1,X0)
          & v3_finset_1(X1)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK2(X0))
        & v2_tops_2(sK2(X0),X0)
        & v3_finset_1(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK2(X0))
            & v2_tops_2(sK2(X0),X0)
            & v3_finset_1(sK2(X0))
            & m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X2] :
              ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
              | ~ v2_tops_2(X2,X0)
              | ~ v3_finset_1(X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f47,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v2_tops_2(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ~ ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                        & v1_finset_1(X2)
                        & r1_tarski(X2,X1)
                        & k1_xboole_0 != X2 ) )
                & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
                & v2_tops_2(X1,X0)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                     => ~ ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                          & v1_finset_1(X2)
                          & r1_tarski(X2,X1)
                          & k1_xboole_0 != X2 ) )
                  & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
                  & v2_tops_2(X1,X0)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                & v1_finset_1(X2)
                & r1_tarski(X2,X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | k1_xboole_0 = X1
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                & v1_finset_1(X2)
                & r1_tarski(X2,X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | k1_xboole_0 = X1
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f17,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> sP0(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f16])).

fof(f33,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,
    ( ? [X0] :
        ( ( ~ sP0(X0)
          | ~ v1_compts_1(X0) )
        & ( sP0(X0)
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ~ sP0(sK5)
        | ~ v1_compts_1(sK5) )
      & ( sP0(sK5)
        | v1_compts_1(sK5) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ sP0(sK5)
      | ~ v1_compts_1(sK5) )
    & ( sP0(sK5)
      | v1_compts_1(sK5) )
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f64,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,
    ( sP0(sK5)
    | v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_finset_1(X0)
    <=> ( ! [X1] :
            ~ ( k1_xboole_0 = k1_setfam_1(X1)
              & v1_finset_1(X1)
              & r1_tarski(X1,X0)
              & k1_xboole_0 != X1 )
        & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( v3_finset_1(X0)
    <=> ( ! [X1] :
            ( k1_xboole_0 != k1_setfam_1(X1)
            | ~ v1_finset_1(X1)
            | ~ r1_tarski(X1,X0)
            | k1_xboole_0 = X1 )
        & k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_finset_1(X0)
        | ? [X1] :
            ( k1_xboole_0 = k1_setfam_1(X1)
            & v1_finset_1(X1)
            & r1_tarski(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = X0 )
      & ( ( ! [X1] :
              ( k1_xboole_0 != k1_setfam_1(X1)
              | ~ v1_finset_1(X1)
              | ~ r1_tarski(X1,X0)
              | k1_xboole_0 = X1 )
          & k1_xboole_0 != X0 )
        | ~ v3_finset_1(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_finset_1(X0)
        | ? [X1] :
            ( k1_xboole_0 = k1_setfam_1(X1)
            & v1_finset_1(X1)
            & r1_tarski(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = X0 )
      & ( ( ! [X1] :
              ( k1_xboole_0 != k1_setfam_1(X1)
              | ~ v1_finset_1(X1)
              | ~ r1_tarski(X1,X0)
              | k1_xboole_0 = X1 )
          & k1_xboole_0 != X0 )
        | ~ v3_finset_1(X0) ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( ( v3_finset_1(X0)
        | ? [X1] :
            ( k1_xboole_0 = k1_setfam_1(X1)
            & v1_finset_1(X1)
            & r1_tarski(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = X0 )
      & ( ( ! [X2] :
              ( k1_xboole_0 != k1_setfam_1(X2)
              | ~ v1_finset_1(X2)
              | ~ r1_tarski(X2,X0)
              | k1_xboole_0 = X2 )
          & k1_xboole_0 != X0 )
        | ~ v3_finset_1(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k1_setfam_1(X1)
          & v1_finset_1(X1)
          & r1_tarski(X1,X0)
          & k1_xboole_0 != X1 )
     => ( k1_xboole_0 = k1_setfam_1(sK1(X0))
        & v1_finset_1(sK1(X0))
        & r1_tarski(sK1(X0),X0)
        & k1_xboole_0 != sK1(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v3_finset_1(X0)
        | ( k1_xboole_0 = k1_setfam_1(sK1(X0))
          & v1_finset_1(sK1(X0))
          & r1_tarski(sK1(X0),X0)
          & k1_xboole_0 != sK1(X0) )
        | k1_xboole_0 = X0 )
      & ( ( ! [X2] :
              ( k1_xboole_0 != k1_setfam_1(X2)
              | ~ v1_finset_1(X2)
              | ~ r1_tarski(X2,X0)
              | k1_xboole_0 = X2 )
          & k1_xboole_0 != X0 )
        | ~ v3_finset_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ~ v3_finset_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f46,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v3_finset_1(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK4(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X3)
      | ~ v2_tops_2(X3,X0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k1_setfam_1(X1) = k6_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k6_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k6_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0] :
      ( v3_finset_1(X0)
      | r1_tarski(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,
    ( ~ sP0(sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_xboole_0 != sK3(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK3(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0] :
      ( sP0(X0)
      | v2_tops_2(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
      | ~ v2_tops_2(X2,X0)
      | ~ v3_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X2,X0] :
      ( sP0(X0)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
      | ~ v1_finset_1(X2)
      | ~ r1_tarski(X2,sK3(X0))
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X0] :
      ( v3_finset_1(X0)
      | k1_xboole_0 != sK1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0] :
      ( v3_finset_1(X0)
      | v1_finset_1(sK1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0] :
      ( v3_finset_1(X0)
      | k1_xboole_0 = k1_setfam_1(sK1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X3] :
      ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK4(X0,X3))
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X3)
      | ~ v2_tops_2(X3,X0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k1_setfam_1(X2)
      | ~ v1_finset_1(X2)
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X2
      | ~ v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X3] :
      ( v1_finset_1(sK4(X0,X3))
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X3)
      | ~ v2_tops_2(X3,X0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X0,X3] :
      ( k1_xboole_0 != sK4(X0,X3)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X3)
      | ~ v2_tops_2(X3,X0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_22,plain,
    ( ~ v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(sK4(X1,X0),X0)
    | ~ sP0(X1)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8,plain,
    ( v2_tops_2(sK2(X0),X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_433,plain,
    ( v2_tops_2(sK2(X0),X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | v1_compts_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_434,plain,
    ( v2_tops_2(sK2(sK5),sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | v1_compts_1(sK5) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_436,plain,
    ( v2_tops_2(sK2(sK5),sK5)
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_29,c_28])).

cnf(c_1135,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(sK4(X1,X0),X0)
    | ~ sP0(X1)
    | v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | sK2(sK5) != X0
    | sK5 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_436])).

cnf(c_1136,plain,
    ( ~ m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | r1_tarski(sK4(sK5,sK2(sK5)),sK2(sK5))
    | ~ sP0(sK5)
    | v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5) ),
    inference(unflattening,[status(thm)],[c_1135])).

cnf(c_26,negated_conjecture,
    ( sP0(sK5)
    | v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_10,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_405,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | v1_compts_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_406,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | v1_compts_1(sK5) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_408,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_29,c_28])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | k6_setfam_1(u1_struct_0(X0),sK2(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_447,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | v1_compts_1(X0)
    | k6_setfam_1(u1_struct_0(X0),sK2(X0)) = k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_448,plain,
    ( v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_450,plain,
    ( v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_29,c_28])).

cnf(c_1138,plain,
    ( v1_compts_1(sK5)
    | r1_tarski(sK4(sK5,sK2(sK5)),sK2(sK5))
    | k1_xboole_0 = sK2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1136,c_29,c_28,c_26,c_406,c_448])).

cnf(c_1139,plain,
    ( r1_tarski(sK4(sK5,sK2(sK5)),sK2(sK5))
    | v1_compts_1(sK5)
    | k1_xboole_0 = sK2(sK5) ),
    inference(renaming,[status(thm)],[c_1138])).

cnf(c_4413,plain,
    ( k1_xboole_0 = sK2(sK5)
    | r1_tarski(sK4(sK5,sK2(sK5)),sK2(sK5)) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_5,plain,
    ( ~ v3_finset_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_90,plain,
    ( v3_finset_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v3_finset_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_419,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | v1_compts_1(X0)
    | v3_finset_1(sK2(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_420,plain,
    ( v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | v1_compts_1(sK5)
    | v3_finset_1(sK2(sK5)) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_422,plain,
    ( v1_compts_1(sK5)
    | v3_finset_1(sK2(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_29,c_28])).

cnf(c_424,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v3_finset_1(sK2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_1140,plain,
    ( k1_xboole_0 = sK2(sK5)
    | r1_tarski(sK4(sK5,sK2(sK5)),sK2(sK5)) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_3842,plain,
    ( ~ v3_finset_1(X0)
    | v3_finset_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4626,plain,
    ( v3_finset_1(X0)
    | ~ v3_finset_1(sK2(sK5))
    | X0 != sK2(sK5) ),
    inference(instantiation,[status(thm)],[c_3842])).

cnf(c_4627,plain,
    ( X0 != sK2(sK5)
    | v3_finset_1(X0) = iProver_top
    | v3_finset_1(sK2(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4626])).

cnf(c_4629,plain,
    ( k1_xboole_0 != sK2(sK5)
    | v3_finset_1(sK2(sK5)) != iProver_top
    | v3_finset_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4627])).

cnf(c_4699,plain,
    ( r1_tarski(sK4(sK5,sK2(sK5)),sK2(sK5)) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4413,c_90,c_424,c_1140,c_4629])).

cnf(c_24,plain,
    ( ~ v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK4(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ sP0(X1)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1101,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK4(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ sP0(X1)
    | v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | sK2(sK5) != X0
    | sK5 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_436])).

cnf(c_1102,plain,
    ( m1_subset_1(sK4(sK5,sK2(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP0(sK5)
    | v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5) ),
    inference(unflattening,[status(thm)],[c_1101])).

cnf(c_1104,plain,
    ( v1_compts_1(sK5)
    | m1_subset_1(sK4(sK5,sK2(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | k1_xboole_0 = sK2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1102,c_29,c_28,c_26,c_406,c_448])).

cnf(c_1105,plain,
    ( m1_subset_1(sK4(sK5,sK2(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v1_compts_1(sK5)
    | k1_xboole_0 = sK2(sK5) ),
    inference(renaming,[status(thm)],[c_1104])).

cnf(c_4415,plain,
    ( k1_xboole_0 = sK2(sK5)
    | m1_subset_1(sK4(sK5,sK2(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1105])).

cnf(c_1106,plain,
    ( k1_xboole_0 = sK2(sK5)
    | m1_subset_1(sK4(sK5,sK2(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1105])).

cnf(c_4706,plain,
    ( m1_subset_1(sK4(sK5,sK2(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4415,c_90,c_424,c_1106,c_4629])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4422,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5086,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_setfam_1(sK4(sK5,sK2(sK5)))
    | v1_compts_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4706,c_4422])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4420,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4418,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_5085,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) = k1_setfam_1(sK2(sK5))
    | v1_compts_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4418,c_4422])).

cnf(c_2,plain,
    ( r1_tarski(sK1(X0),X0)
    | v3_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4426,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(sK1(X0),X0) = iProver_top
    | v3_finset_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_19,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( ~ sP0(sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_237,plain,
    ( ~ sP0(sK5)
    | ~ v1_compts_1(sK5) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_1234,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ v1_compts_1(sK5)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_237])).

cnf(c_1235,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ v1_compts_1(sK5) ),
    inference(unflattening,[status(thm)],[c_1234])).

cnf(c_4410,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4419,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4999,plain,
    ( r1_tarski(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4410,c_4419])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4421,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5610,plain,
    ( r1_tarski(X0,sK3(sK5)) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4999,c_4421])).

cnf(c_5084,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4420,c_4422])).

cnf(c_6367,plain,
    ( k6_setfam_1(u1_struct_0(sK5),X0) = k1_setfam_1(X0)
    | r1_tarski(X0,sK3(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5610,c_5084])).

cnf(c_7563,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK1(sK3(sK5))) = k1_setfam_1(sK1(sK3(sK5)))
    | sK3(sK5) = k1_xboole_0
    | v1_compts_1(sK5) != iProver_top
    | v3_finset_1(sK3(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4426,c_6367])).

cnf(c_18,plain,
    ( sP0(X0)
    | sK3(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1244,plain,
    ( ~ v1_compts_1(sK5)
    | sK3(X0) != k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_237])).

cnf(c_1245,plain,
    ( ~ v1_compts_1(sK5)
    | sK3(sK5) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1244])).

cnf(c_1246,plain,
    ( sK3(sK5) != k1_xboole_0
    | v1_compts_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_16,plain,
    ( sP0(X0)
    | k6_setfam_1(u1_struct_0(X0),sK3(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1254,plain,
    ( ~ v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(X0),sK3(X0)) = k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_237])).

cnf(c_1255,plain,
    ( ~ v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(sK5),sK3(sK5)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1254])).

cnf(c_1256,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK3(sK5)) = k1_xboole_0
    | v1_compts_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1255])).

cnf(c_17,plain,
    ( v2_tops_2(sK3(X0),X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11,plain,
    ( ~ v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ v3_finset_1(X0)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_461,plain,
    ( ~ v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ v3_finset_1(X0)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_462,plain,
    ( ~ v2_tops_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ v1_compts_1(sK5)
    | ~ v3_finset_1(X0)
    | k6_setfam_1(u1_struct_0(sK5),X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_464,plain,
    ( ~ v2_tops_2(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ v1_compts_1(sK5)
    | ~ v3_finset_1(X0)
    | k6_setfam_1(u1_struct_0(sK5),X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_29,c_28])).

cnf(c_1186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | sP0(X1)
    | ~ v1_compts_1(sK5)
    | ~ v3_finset_1(X0)
    | k6_setfam_1(u1_struct_0(sK5),X0) != k1_xboole_0
    | sK3(X1) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_464])).

cnf(c_1187,plain,
    ( ~ m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | sP0(sK5)
    | ~ v1_compts_1(sK5)
    | ~ v3_finset_1(sK3(sK5))
    | k6_setfam_1(u1_struct_0(sK5),sK3(sK5)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_1189,plain,
    ( ~ m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ v1_compts_1(sK5)
    | ~ v3_finset_1(sK3(sK5))
    | k6_setfam_1(u1_struct_0(sK5),sK3(sK5)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1187,c_25])).

cnf(c_1289,plain,
    ( ~ v1_compts_1(sK5)
    | ~ v3_finset_1(sK3(sK5))
    | k6_setfam_1(u1_struct_0(sK5),sK3(sK5)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1235,c_1189])).

cnf(c_1291,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK3(sK5)) != k1_xboole_0
    | v1_compts_1(sK5) != iProver_top
    | v3_finset_1(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1289])).

cnf(c_7742,plain,
    ( v1_compts_1(sK5) != iProver_top
    | k6_setfam_1(u1_struct_0(sK5),sK1(sK3(sK5))) = k1_setfam_1(sK1(sK3(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7563,c_1246,c_1256,c_1291])).

cnf(c_7743,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK1(sK3(sK5))) = k1_setfam_1(sK1(sK3(sK5)))
    | v1_compts_1(sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_7742])).

cnf(c_7749,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) = k1_setfam_1(sK2(sK5))
    | k6_setfam_1(u1_struct_0(sK5),sK1(sK3(sK5))) = k1_setfam_1(sK1(sK3(sK5))) ),
    inference(superposition,[status(thm)],[c_5085,c_7743])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,sK3(X1))
    | sP0(X1)
    | ~ v1_finset_1(X0)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,sK3(X1))
    | ~ v1_compts_1(sK5)
    | ~ v1_finset_1(X0)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | sK5 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_237])).

cnf(c_1265,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r1_tarski(X0,sK3(sK5))
    | ~ v1_compts_1(sK5)
    | ~ v1_finset_1(X0)
    | k6_setfam_1(u1_struct_0(sK5),X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1264])).

cnf(c_4407,plain,
    ( k6_setfam_1(u1_struct_0(sK5),X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(X0,sK3(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_7958,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) = k1_setfam_1(sK2(sK5))
    | k1_setfam_1(sK1(sK3(sK5))) != k1_xboole_0
    | sK1(sK3(sK5)) = k1_xboole_0
    | m1_subset_1(sK1(sK3(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(sK1(sK3(sK5)),sK3(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v1_finset_1(sK1(sK3(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7749,c_4407])).

cnf(c_3,plain,
    ( v3_finset_1(X0)
    | sK1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1298,plain,
    ( ~ v1_compts_1(sK5)
    | ~ v3_finset_1(sK3(sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1255,c_1289])).

cnf(c_1697,plain,
    ( ~ v1_compts_1(sK5)
    | sK3(sK5) != X0
    | sK1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_1298])).

cnf(c_1698,plain,
    ( ~ v1_compts_1(sK5)
    | sK1(sK3(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK3(sK5) ),
    inference(unflattening,[status(thm)],[c_1697])).

cnf(c_1699,plain,
    ( sK1(sK3(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK3(sK5)
    | v1_compts_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1698])).

cnf(c_1710,plain,
    ( r1_tarski(sK1(X0),X0)
    | ~ v1_compts_1(sK5)
    | sK3(sK5) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_1298])).

cnf(c_1711,plain,
    ( r1_tarski(sK1(sK3(sK5)),sK3(sK5))
    | ~ v1_compts_1(sK5)
    | k1_xboole_0 = sK3(sK5) ),
    inference(unflattening,[status(thm)],[c_1710])).

cnf(c_1712,plain,
    ( k1_xboole_0 = sK3(sK5)
    | r1_tarski(sK1(sK3(sK5)),sK3(sK5)) = iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1711])).

cnf(c_1,plain,
    ( v1_finset_1(sK1(X0))
    | v3_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1723,plain,
    ( ~ v1_compts_1(sK5)
    | v1_finset_1(sK1(X0))
    | sK3(sK5) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_1298])).

cnf(c_1724,plain,
    ( ~ v1_compts_1(sK5)
    | v1_finset_1(sK1(sK3(sK5)))
    | k1_xboole_0 = sK3(sK5) ),
    inference(unflattening,[status(thm)],[c_1723])).

cnf(c_1725,plain,
    ( k1_xboole_0 = sK3(sK5)
    | v1_compts_1(sK5) != iProver_top
    | v1_finset_1(sK1(sK3(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1724])).

cnf(c_3841,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4827,plain,
    ( sK3(sK5) != X0
    | sK3(sK5) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_3841])).

cnf(c_5023,plain,
    ( sK3(sK5) != sK3(sK5)
    | sK3(sK5) = k1_xboole_0
    | k1_xboole_0 != sK3(sK5) ),
    inference(instantiation,[status(thm)],[c_4827])).

cnf(c_3840,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5024,plain,
    ( sK3(sK5) = sK3(sK5) ),
    inference(instantiation,[status(thm)],[c_3840])).

cnf(c_6220,plain,
    ( sK1(sK3(sK5)) != X0
    | sK1(sK3(sK5)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_3841])).

cnf(c_7778,plain,
    ( sK1(sK3(sK5)) != sK1(sK3(sK5))
    | sK1(sK3(sK5)) = k1_xboole_0
    | k1_xboole_0 != sK1(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_6220])).

cnf(c_7779,plain,
    ( sK1(sK3(sK5)) = sK1(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_3840])).

cnf(c_7821,plain,
    ( ~ m1_subset_1(sK1(sK3(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r1_tarski(sK1(sK3(sK5)),sK3(sK5))
    | ~ v1_compts_1(sK5)
    | ~ v1_finset_1(sK1(sK3(sK5)))
    | k6_setfam_1(u1_struct_0(sK5),sK1(sK3(sK5))) != k1_xboole_0
    | k1_xboole_0 = sK1(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_7836,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK1(sK3(sK5))) != k1_xboole_0
    | k1_xboole_0 = sK1(sK3(sK5))
    | m1_subset_1(sK1(sK3(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(sK1(sK3(sK5)),sK3(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v1_finset_1(sK1(sK3(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7821])).

cnf(c_0,plain,
    ( v3_finset_1(X0)
    | k1_setfam_1(sK1(X0)) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4428,plain,
    ( k1_setfam_1(sK1(X0)) = k1_xboole_0
    | k1_xboole_0 = X0
    | v3_finset_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4406,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v3_finset_1(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_5073,plain,
    ( sK3(sK5) = k1_xboole_0
    | k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0
    | v1_compts_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4428,c_4406])).

cnf(c_5457,plain,
    ( k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0
    | v1_compts_1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5073,c_1246])).

cnf(c_5463,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_setfam_1(sK4(sK5,sK2(sK5)))
    | k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5086,c_5457])).

cnf(c_20,plain,
    ( ~ v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ sP0(X1)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | k6_setfam_1(u1_struct_0(X1),sK4(X1,X0)) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1169,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ sP0(X1)
    | v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | k6_setfam_1(u1_struct_0(X1),sK4(X1,X0)) = k1_xboole_0
    | sK2(sK5) != X0
    | sK5 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_436])).

cnf(c_1170,plain,
    ( ~ m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP0(sK5)
    | v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5) ),
    inference(unflattening,[status(thm)],[c_1169])).

cnf(c_1172,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_xboole_0
    | v1_compts_1(sK5)
    | k1_xboole_0 = sK2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_29,c_28,c_26,c_406,c_448])).

cnf(c_1173,plain,
    ( v1_compts_1(sK5)
    | k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_xboole_0
    | k1_xboole_0 = sK2(sK5) ),
    inference(renaming,[status(thm)],[c_1172])).

cnf(c_4411,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_xboole_0
    | k1_xboole_0 = sK2(sK5)
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_1174,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_xboole_0
    | k1_xboole_0 = sK2(sK5)
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_4655,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_xboole_0
    | v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4411,c_90,c_424,c_1174,c_4629])).

cnf(c_5465,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_xboole_0
    | k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4655,c_5457])).

cnf(c_6260,plain,
    ( k1_setfam_1(sK4(sK5,sK2(sK5))) = k1_xboole_0
    | k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5463,c_5465])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_finset_1(X0)
    | ~ v3_finset_1(X1)
    | k1_setfam_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4424,plain,
    ( k1_setfam_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v3_finset_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6406,plain,
    ( sK4(sK5,sK2(sK5)) = k1_xboole_0
    | k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0
    | r1_tarski(sK4(sK5,sK2(sK5)),X0) != iProver_top
    | v1_finset_1(sK4(sK5,sK2(sK5))) != iProver_top
    | v3_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6260,c_4424])).

cnf(c_21,plain,
    ( ~ v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ sP0(X1)
    | v1_finset_1(sK4(X1,X0))
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1152,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ sP0(X1)
    | v1_compts_1(sK5)
    | v1_finset_1(sK4(X1,X0))
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | sK2(sK5) != X0
    | sK5 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_436])).

cnf(c_1153,plain,
    ( ~ m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP0(sK5)
    | v1_compts_1(sK5)
    | v1_finset_1(sK4(sK5,sK2(sK5)))
    | k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5) ),
    inference(unflattening,[status(thm)],[c_1152])).

cnf(c_1155,plain,
    ( v1_finset_1(sK4(sK5,sK2(sK5)))
    | v1_compts_1(sK5)
    | k1_xboole_0 = sK2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1153,c_29,c_28,c_26,c_406,c_448])).

cnf(c_1156,plain,
    ( v1_compts_1(sK5)
    | v1_finset_1(sK4(sK5,sK2(sK5)))
    | k1_xboole_0 = sK2(sK5) ),
    inference(renaming,[status(thm)],[c_1155])).

cnf(c_1360,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_compts_1(sK5)
    | ~ v3_finset_1(X1)
    | sK4(sK5,sK2(sK5)) != X0
    | sK2(sK5) = k1_xboole_0
    | k1_setfam_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_1156])).

cnf(c_1361,plain,
    ( ~ r1_tarski(sK4(sK5,sK2(sK5)),X0)
    | v1_compts_1(sK5)
    | ~ v3_finset_1(X0)
    | sK2(sK5) = k1_xboole_0
    | k1_setfam_1(sK4(sK5,sK2(sK5))) != k1_xboole_0
    | k1_xboole_0 = sK4(sK5,sK2(sK5)) ),
    inference(unflattening,[status(thm)],[c_1360])).

cnf(c_1027,plain,
    ( v1_compts_1(sK5)
    | sK2(sK5) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_422])).

cnf(c_1363,plain,
    ( ~ v3_finset_1(X0)
    | v1_compts_1(sK5)
    | ~ r1_tarski(sK4(sK5,sK2(sK5)),X0)
    | k1_setfam_1(sK4(sK5,sK2(sK5))) != k1_xboole_0
    | k1_xboole_0 = sK4(sK5,sK2(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1361,c_1027])).

cnf(c_1364,plain,
    ( ~ r1_tarski(sK4(sK5,sK2(sK5)),X0)
    | v1_compts_1(sK5)
    | ~ v3_finset_1(X0)
    | k1_setfam_1(sK4(sK5,sK2(sK5))) != k1_xboole_0
    | k1_xboole_0 = sK4(sK5,sK2(sK5)) ),
    inference(renaming,[status(thm)],[c_1363])).

cnf(c_1365,plain,
    ( k1_setfam_1(sK4(sK5,sK2(sK5))) != k1_xboole_0
    | k1_xboole_0 = sK4(sK5,sK2(sK5))
    | r1_tarski(sK4(sK5,sK2(sK5)),X0) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v3_finset_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1364])).

cnf(c_23,plain,
    ( ~ v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ sP0(X1)
    | sK4(X1,X0) != k1_xboole_0
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1118,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ sP0(X1)
    | v1_compts_1(sK5)
    | sK4(X1,X0) != k1_xboole_0
    | k6_setfam_1(u1_struct_0(X1),X0) != k1_xboole_0
    | sK2(sK5) != X0
    | sK5 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_436])).

cnf(c_1119,plain,
    ( ~ m1_subset_1(sK2(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP0(sK5)
    | v1_compts_1(sK5)
    | sK4(sK5,sK2(sK5)) != k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK5),sK2(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5) ),
    inference(unflattening,[status(thm)],[c_1118])).

cnf(c_1121,plain,
    ( sK4(sK5,sK2(sK5)) != k1_xboole_0
    | v1_compts_1(sK5)
    | k1_xboole_0 = sK2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1119,c_29,c_28,c_26,c_406,c_448])).

cnf(c_1122,plain,
    ( v1_compts_1(sK5)
    | sK4(sK5,sK2(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5) ),
    inference(renaming,[status(thm)],[c_1121])).

cnf(c_4414,plain,
    ( sK4(sK5,sK2(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5)
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_1123,plain,
    ( sK4(sK5,sK2(sK5)) != k1_xboole_0
    | k1_xboole_0 = sK2(sK5)
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_4648,plain,
    ( sK4(sK5,sK2(sK5)) != k1_xboole_0
    | v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4414,c_90,c_424,c_1123,c_4629])).

cnf(c_4661,plain,
    ( sK4(sK5,sK2(sK5)) != X0
    | sK4(sK5,sK2(sK5)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_3841])).

cnf(c_4876,plain,
    ( sK4(sK5,sK2(sK5)) != sK4(sK5,sK2(sK5))
    | sK4(sK5,sK2(sK5)) = k1_xboole_0
    | k1_xboole_0 != sK4(sK5,sK2(sK5)) ),
    inference(instantiation,[status(thm)],[c_4661])).

cnf(c_4877,plain,
    ( sK4(sK5,sK2(sK5)) = sK4(sK5,sK2(sK5)) ),
    inference(instantiation,[status(thm)],[c_3840])).

cnf(c_8377,plain,
    ( r1_tarski(sK4(sK5,sK2(sK5)),X0) != iProver_top
    | k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0
    | v3_finset_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6406,c_1246,c_1365,c_4648,c_4876,c_4877,c_5073,c_6260])).

cnf(c_8378,plain,
    ( k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0
    | r1_tarski(sK4(sK5,sK2(sK5)),X0) != iProver_top
    | v3_finset_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8377])).

cnf(c_8384,plain,
    ( k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0
    | v1_compts_1(sK5) = iProver_top
    | v3_finset_1(sK2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4699,c_8378])).

cnf(c_8805,plain,
    ( k1_setfam_1(sK1(sK3(sK5))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8384,c_424,c_5457])).

cnf(c_8809,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK1(sK3(sK5))) = k1_xboole_0
    | v1_compts_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8805,c_7743])).

cnf(c_10331,plain,
    ( v1_compts_1(sK5) != iProver_top
    | m1_subset_1(sK1(sK3(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7958,c_1246,c_1699,c_1712,c_1725,c_5023,c_5024,c_7778,c_7779,c_7836,c_8809])).

cnf(c_10332,plain,
    ( m1_subset_1(sK1(sK3(sK5)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_10331])).

cnf(c_10337,plain,
    ( r1_tarski(sK1(sK3(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4420,c_10332])).

cnf(c_4963,plain,
    ( ~ r1_tarski(X0,sK3(sK5))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6217,plain,
    ( ~ r1_tarski(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(sK1(sK3(sK5)),sK3(sK5))
    | r1_tarski(sK1(sK3(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_4963])).

cnf(c_6218,plain,
    ( r1_tarski(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(sK1(sK3(sK5)),sK3(sK5)) != iProver_top
    | r1_tarski(sK1(sK3(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6217])).

cnf(c_10466,plain,
    ( v1_compts_1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10337,c_1246,c_1712,c_4999,c_5023,c_5024,c_6218])).

cnf(c_10472,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_setfam_1(sK4(sK5,sK2(sK5))) ),
    inference(superposition,[status(thm)],[c_5086,c_10466])).

cnf(c_10473,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(sK5,sK2(sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4655,c_10466])).

cnf(c_10476,plain,
    ( k1_setfam_1(sK4(sK5,sK2(sK5))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10472,c_10473])).

cnf(c_10607,plain,
    ( sK4(sK5,sK2(sK5)) = k1_xboole_0
    | r1_tarski(sK4(sK5,sK2(sK5)),X0) != iProver_top
    | v1_finset_1(sK4(sK5,sK2(sK5))) != iProver_top
    | v3_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10476,c_4424])).

cnf(c_1157,plain,
    ( k1_xboole_0 = sK2(sK5)
    | v1_compts_1(sK5) = iProver_top
    | v1_finset_1(sK4(sK5,sK2(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_10720,plain,
    ( r1_tarski(sK4(sK5,sK2(sK5)),X0) != iProver_top
    | v3_finset_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10607,c_1246,c_1365,c_1712,c_4648,c_4876,c_4877,c_4999,c_5023,c_5024,c_6218,c_10337,c_10476])).

cnf(c_10726,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v3_finset_1(sK2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4699,c_10720])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10726,c_10466,c_424])).


%------------------------------------------------------------------------------

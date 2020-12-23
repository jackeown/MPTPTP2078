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
% DateTime   : Thu Dec  3 12:18:48 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 234 expanded)
%              Number of clauses        :   57 (  73 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  313 ( 775 expanded)
%              Number of equality atoms :   72 (  95 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m2_connsp_2(k2_struct_0(X0),X0,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f34,f33])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f55,plain,(
    ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_362,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k2_subset_1(X2) != X0
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_363,plain,
    ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_424,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_subset_1(X2),k1_zfmisc_1(X2))
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_363])).

cnf(c_425,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r2_hidden(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_659,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_683,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_425,c_659])).

cnf(c_748,plain,
    ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0))
    | X0 != X1
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_683])).

cnf(c_749,plain,
    ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_748])).

cnf(c_1320,plain,
    ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1333,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1320,c_6])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_388,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_389,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_436,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_389])).

cnf(c_437,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_1322,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_242,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_9])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_338,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_242,c_16])).

cnf(c_339,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_1353,plain,
    ( r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1322,c_339])).

cnf(c_1533,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_1353])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1506,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1507,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1)) = iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_14,negated_conjecture,
    ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_295,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_296,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_300,plain,
    ( ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_16])).

cnf(c_301,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_300])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | k2_struct_0(sK1) != X0
    | sK2 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_301])).

cnf(c_346,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_348,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_15])).

cnf(c_374,plain,
    ( ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1)))
    | k2_subset_1(X0) != k2_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_7,c_348])).

cnf(c_1323,plain,
    ( k2_subset_1(X0) != k2_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
    | r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_11,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_319,plain,
    ( ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_320,plain,
    ( ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_29,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_322,plain,
    ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_17,c_16,c_29])).

cnf(c_1370,plain,
    ( k2_struct_0(sK1) != X0
    | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0)
    | r1_tarski(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1323,c_6,c_322,c_339])).

cnf(c_1474,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | r1_tarski(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1370])).

cnf(c_1055,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1074,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_1062,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_1070,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1533,c_1507,c_1474,c_1074,c_1070])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:36:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.38/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.38/0.99  
% 1.38/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.38/0.99  
% 1.38/0.99  ------  iProver source info
% 1.38/0.99  
% 1.38/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.38/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.38/0.99  git: non_committed_changes: false
% 1.38/0.99  git: last_make_outside_of_git: false
% 1.38/0.99  
% 1.38/0.99  ------ 
% 1.38/0.99  
% 1.38/0.99  ------ Input Options
% 1.38/0.99  
% 1.38/0.99  --out_options                           all
% 1.38/0.99  --tptp_safe_out                         true
% 1.38/0.99  --problem_path                          ""
% 1.38/0.99  --include_path                          ""
% 1.38/0.99  --clausifier                            res/vclausify_rel
% 1.38/0.99  --clausifier_options                    --mode clausify
% 1.38/0.99  --stdin                                 false
% 1.38/0.99  --stats_out                             all
% 1.38/0.99  
% 1.38/0.99  ------ General Options
% 1.38/0.99  
% 1.38/0.99  --fof                                   false
% 1.38/0.99  --time_out_real                         305.
% 1.38/0.99  --time_out_virtual                      -1.
% 1.38/0.99  --symbol_type_check                     false
% 1.38/0.99  --clausify_out                          false
% 1.38/0.99  --sig_cnt_out                           false
% 1.38/0.99  --trig_cnt_out                          false
% 1.38/0.99  --trig_cnt_out_tolerance                1.
% 1.38/0.99  --trig_cnt_out_sk_spl                   false
% 1.38/0.99  --abstr_cl_out                          false
% 1.38/0.99  
% 1.38/0.99  ------ Global Options
% 1.38/0.99  
% 1.38/0.99  --schedule                              default
% 1.38/0.99  --add_important_lit                     false
% 1.38/0.99  --prop_solver_per_cl                    1000
% 1.38/0.99  --min_unsat_core                        false
% 1.38/0.99  --soft_assumptions                      false
% 1.38/0.99  --soft_lemma_size                       3
% 1.38/0.99  --prop_impl_unit_size                   0
% 1.38/0.99  --prop_impl_unit                        []
% 1.38/0.99  --share_sel_clauses                     true
% 1.38/0.99  --reset_solvers                         false
% 1.38/0.99  --bc_imp_inh                            [conj_cone]
% 1.38/0.99  --conj_cone_tolerance                   3.
% 1.38/0.99  --extra_neg_conj                        none
% 1.38/0.99  --large_theory_mode                     true
% 1.38/0.99  --prolific_symb_bound                   200
% 1.38/0.99  --lt_threshold                          2000
% 1.38/0.99  --clause_weak_htbl                      true
% 1.38/0.99  --gc_record_bc_elim                     false
% 1.38/0.99  
% 1.38/0.99  ------ Preprocessing Options
% 1.38/0.99  
% 1.38/0.99  --preprocessing_flag                    true
% 1.38/0.99  --time_out_prep_mult                    0.1
% 1.38/0.99  --splitting_mode                        input
% 1.38/0.99  --splitting_grd                         true
% 1.38/0.99  --splitting_cvd                         false
% 1.38/0.99  --splitting_cvd_svl                     false
% 1.38/0.99  --splitting_nvd                         32
% 1.38/0.99  --sub_typing                            true
% 1.38/0.99  --prep_gs_sim                           true
% 1.38/0.99  --prep_unflatten                        true
% 1.38/0.99  --prep_res_sim                          true
% 1.38/0.99  --prep_upred                            true
% 1.38/0.99  --prep_sem_filter                       exhaustive
% 1.38/0.99  --prep_sem_filter_out                   false
% 1.38/0.99  --pred_elim                             true
% 1.38/0.99  --res_sim_input                         true
% 1.38/0.99  --eq_ax_congr_red                       true
% 1.38/0.99  --pure_diseq_elim                       true
% 1.38/0.99  --brand_transform                       false
% 1.38/0.99  --non_eq_to_eq                          false
% 1.38/0.99  --prep_def_merge                        true
% 1.38/0.99  --prep_def_merge_prop_impl              false
% 1.38/1.00  --prep_def_merge_mbd                    true
% 1.38/1.00  --prep_def_merge_tr_red                 false
% 1.38/1.00  --prep_def_merge_tr_cl                  false
% 1.38/1.00  --smt_preprocessing                     true
% 1.38/1.00  --smt_ac_axioms                         fast
% 1.38/1.00  --preprocessed_out                      false
% 1.38/1.00  --preprocessed_stats                    false
% 1.38/1.00  
% 1.38/1.00  ------ Abstraction refinement Options
% 1.38/1.00  
% 1.38/1.00  --abstr_ref                             []
% 1.38/1.00  --abstr_ref_prep                        false
% 1.38/1.00  --abstr_ref_until_sat                   false
% 1.38/1.00  --abstr_ref_sig_restrict                funpre
% 1.38/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.38/1.00  --abstr_ref_under                       []
% 1.38/1.00  
% 1.38/1.00  ------ SAT Options
% 1.38/1.00  
% 1.38/1.00  --sat_mode                              false
% 1.38/1.00  --sat_fm_restart_options                ""
% 1.38/1.00  --sat_gr_def                            false
% 1.38/1.00  --sat_epr_types                         true
% 1.38/1.00  --sat_non_cyclic_types                  false
% 1.38/1.00  --sat_finite_models                     false
% 1.38/1.00  --sat_fm_lemmas                         false
% 1.38/1.00  --sat_fm_prep                           false
% 1.38/1.00  --sat_fm_uc_incr                        true
% 1.38/1.00  --sat_out_model                         small
% 1.38/1.00  --sat_out_clauses                       false
% 1.38/1.00  
% 1.38/1.00  ------ QBF Options
% 1.38/1.00  
% 1.38/1.00  --qbf_mode                              false
% 1.38/1.00  --qbf_elim_univ                         false
% 1.38/1.00  --qbf_dom_inst                          none
% 1.38/1.00  --qbf_dom_pre_inst                      false
% 1.38/1.00  --qbf_sk_in                             false
% 1.38/1.00  --qbf_pred_elim                         true
% 1.38/1.00  --qbf_split                             512
% 1.38/1.00  
% 1.38/1.00  ------ BMC1 Options
% 1.38/1.00  
% 1.38/1.00  --bmc1_incremental                      false
% 1.38/1.00  --bmc1_axioms                           reachable_all
% 1.38/1.00  --bmc1_min_bound                        0
% 1.38/1.00  --bmc1_max_bound                        -1
% 1.38/1.00  --bmc1_max_bound_default                -1
% 1.38/1.00  --bmc1_symbol_reachability              true
% 1.38/1.00  --bmc1_property_lemmas                  false
% 1.38/1.00  --bmc1_k_induction                      false
% 1.38/1.00  --bmc1_non_equiv_states                 false
% 1.38/1.00  --bmc1_deadlock                         false
% 1.38/1.00  --bmc1_ucm                              false
% 1.38/1.00  --bmc1_add_unsat_core                   none
% 1.38/1.00  --bmc1_unsat_core_children              false
% 1.38/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.38/1.00  --bmc1_out_stat                         full
% 1.38/1.00  --bmc1_ground_init                      false
% 1.38/1.00  --bmc1_pre_inst_next_state              false
% 1.38/1.00  --bmc1_pre_inst_state                   false
% 1.38/1.00  --bmc1_pre_inst_reach_state             false
% 1.38/1.00  --bmc1_out_unsat_core                   false
% 1.38/1.00  --bmc1_aig_witness_out                  false
% 1.38/1.00  --bmc1_verbose                          false
% 1.38/1.00  --bmc1_dump_clauses_tptp                false
% 1.38/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.38/1.00  --bmc1_dump_file                        -
% 1.38/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.38/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.38/1.00  --bmc1_ucm_extend_mode                  1
% 1.38/1.00  --bmc1_ucm_init_mode                    2
% 1.38/1.00  --bmc1_ucm_cone_mode                    none
% 1.38/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.38/1.00  --bmc1_ucm_relax_model                  4
% 1.38/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.38/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.38/1.00  --bmc1_ucm_layered_model                none
% 1.38/1.00  --bmc1_ucm_max_lemma_size               10
% 1.38/1.00  
% 1.38/1.00  ------ AIG Options
% 1.38/1.00  
% 1.38/1.00  --aig_mode                              false
% 1.38/1.00  
% 1.38/1.00  ------ Instantiation Options
% 1.38/1.00  
% 1.38/1.00  --instantiation_flag                    true
% 1.38/1.00  --inst_sos_flag                         false
% 1.38/1.00  --inst_sos_phase                        true
% 1.38/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.38/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.38/1.00  --inst_lit_sel_side                     num_symb
% 1.38/1.00  --inst_solver_per_active                1400
% 1.38/1.00  --inst_solver_calls_frac                1.
% 1.38/1.00  --inst_passive_queue_type               priority_queues
% 1.38/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.38/1.00  --inst_passive_queues_freq              [25;2]
% 1.38/1.00  --inst_dismatching                      true
% 1.38/1.00  --inst_eager_unprocessed_to_passive     true
% 1.38/1.00  --inst_prop_sim_given                   true
% 1.38/1.00  --inst_prop_sim_new                     false
% 1.38/1.00  --inst_subs_new                         false
% 1.38/1.00  --inst_eq_res_simp                      false
% 1.38/1.00  --inst_subs_given                       false
% 1.38/1.00  --inst_orphan_elimination               true
% 1.38/1.00  --inst_learning_loop_flag               true
% 1.38/1.00  --inst_learning_start                   3000
% 1.38/1.00  --inst_learning_factor                  2
% 1.38/1.00  --inst_start_prop_sim_after_learn       3
% 1.38/1.00  --inst_sel_renew                        solver
% 1.38/1.00  --inst_lit_activity_flag                true
% 1.38/1.00  --inst_restr_to_given                   false
% 1.38/1.00  --inst_activity_threshold               500
% 1.38/1.00  --inst_out_proof                        true
% 1.38/1.00  
% 1.38/1.00  ------ Resolution Options
% 1.38/1.00  
% 1.38/1.00  --resolution_flag                       true
% 1.38/1.00  --res_lit_sel                           adaptive
% 1.38/1.00  --res_lit_sel_side                      none
% 1.38/1.00  --res_ordering                          kbo
% 1.38/1.00  --res_to_prop_solver                    active
% 1.38/1.00  --res_prop_simpl_new                    false
% 1.38/1.00  --res_prop_simpl_given                  true
% 1.38/1.00  --res_passive_queue_type                priority_queues
% 1.38/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.38/1.00  --res_passive_queues_freq               [15;5]
% 1.38/1.00  --res_forward_subs                      full
% 1.38/1.00  --res_backward_subs                     full
% 1.38/1.00  --res_forward_subs_resolution           true
% 1.38/1.00  --res_backward_subs_resolution          true
% 1.38/1.00  --res_orphan_elimination                true
% 1.38/1.00  --res_time_limit                        2.
% 1.38/1.00  --res_out_proof                         true
% 1.38/1.00  
% 1.38/1.00  ------ Superposition Options
% 1.38/1.00  
% 1.38/1.00  --superposition_flag                    true
% 1.38/1.00  --sup_passive_queue_type                priority_queues
% 1.38/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.38/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.38/1.00  --demod_completeness_check              fast
% 1.38/1.00  --demod_use_ground                      true
% 1.38/1.00  --sup_to_prop_solver                    passive
% 1.38/1.00  --sup_prop_simpl_new                    true
% 1.38/1.00  --sup_prop_simpl_given                  true
% 1.38/1.00  --sup_fun_splitting                     false
% 1.38/1.00  --sup_smt_interval                      50000
% 1.38/1.00  
% 1.38/1.00  ------ Superposition Simplification Setup
% 1.38/1.00  
% 1.38/1.00  --sup_indices_passive                   []
% 1.38/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.38/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.38/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.38/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.38/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.38/1.00  --sup_full_bw                           [BwDemod]
% 1.38/1.00  --sup_immed_triv                        [TrivRules]
% 1.38/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.38/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.38/1.00  --sup_immed_bw_main                     []
% 1.38/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.38/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.38/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.38/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.38/1.00  
% 1.38/1.00  ------ Combination Options
% 1.38/1.00  
% 1.38/1.00  --comb_res_mult                         3
% 1.38/1.00  --comb_sup_mult                         2
% 1.38/1.00  --comb_inst_mult                        10
% 1.38/1.00  
% 1.38/1.00  ------ Debug Options
% 1.38/1.00  
% 1.38/1.00  --dbg_backtrace                         false
% 1.38/1.00  --dbg_dump_prop_clauses                 false
% 1.38/1.00  --dbg_dump_prop_clauses_file            -
% 1.38/1.00  --dbg_out_stat                          false
% 1.38/1.00  ------ Parsing...
% 1.38/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.38/1.00  
% 1.38/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.38/1.00  
% 1.38/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.38/1.00  
% 1.38/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.38/1.00  ------ Proving...
% 1.38/1.00  ------ Problem Properties 
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  clauses                                 12
% 1.38/1.00  conjectures                             0
% 1.38/1.00  EPR                                     0
% 1.38/1.00  Horn                                    11
% 1.38/1.00  unary                                   5
% 1.38/1.00  binary                                  4
% 1.38/1.00  lits                                    22
% 1.38/1.00  lits eq                                 8
% 1.38/1.00  fd_pure                                 0
% 1.38/1.00  fd_pseudo                               0
% 1.38/1.00  fd_cond                                 0
% 1.38/1.00  fd_pseudo_cond                          2
% 1.38/1.00  AC symbols                              0
% 1.38/1.00  
% 1.38/1.00  ------ Schedule dynamic 5 is on 
% 1.38/1.00  
% 1.38/1.00  ------ no conjectures: strip conj schedule 
% 1.38/1.00  
% 1.38/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  ------ 
% 1.38/1.00  Current options:
% 1.38/1.00  ------ 
% 1.38/1.00  
% 1.38/1.00  ------ Input Options
% 1.38/1.00  
% 1.38/1.00  --out_options                           all
% 1.38/1.00  --tptp_safe_out                         true
% 1.38/1.00  --problem_path                          ""
% 1.38/1.00  --include_path                          ""
% 1.38/1.00  --clausifier                            res/vclausify_rel
% 1.38/1.00  --clausifier_options                    --mode clausify
% 1.38/1.00  --stdin                                 false
% 1.38/1.00  --stats_out                             all
% 1.38/1.00  
% 1.38/1.00  ------ General Options
% 1.38/1.00  
% 1.38/1.00  --fof                                   false
% 1.38/1.00  --time_out_real                         305.
% 1.38/1.00  --time_out_virtual                      -1.
% 1.38/1.00  --symbol_type_check                     false
% 1.38/1.00  --clausify_out                          false
% 1.38/1.00  --sig_cnt_out                           false
% 1.38/1.00  --trig_cnt_out                          false
% 1.38/1.00  --trig_cnt_out_tolerance                1.
% 1.38/1.00  --trig_cnt_out_sk_spl                   false
% 1.38/1.00  --abstr_cl_out                          false
% 1.38/1.00  
% 1.38/1.00  ------ Global Options
% 1.38/1.00  
% 1.38/1.00  --schedule                              default
% 1.38/1.00  --add_important_lit                     false
% 1.38/1.00  --prop_solver_per_cl                    1000
% 1.38/1.00  --min_unsat_core                        false
% 1.38/1.00  --soft_assumptions                      false
% 1.38/1.00  --soft_lemma_size                       3
% 1.38/1.00  --prop_impl_unit_size                   0
% 1.38/1.00  --prop_impl_unit                        []
% 1.38/1.00  --share_sel_clauses                     true
% 1.38/1.00  --reset_solvers                         false
% 1.38/1.00  --bc_imp_inh                            [conj_cone]
% 1.38/1.00  --conj_cone_tolerance                   3.
% 1.38/1.00  --extra_neg_conj                        none
% 1.38/1.00  --large_theory_mode                     true
% 1.38/1.00  --prolific_symb_bound                   200
% 1.38/1.00  --lt_threshold                          2000
% 1.38/1.00  --clause_weak_htbl                      true
% 1.38/1.00  --gc_record_bc_elim                     false
% 1.38/1.00  
% 1.38/1.00  ------ Preprocessing Options
% 1.38/1.00  
% 1.38/1.00  --preprocessing_flag                    true
% 1.38/1.00  --time_out_prep_mult                    0.1
% 1.38/1.00  --splitting_mode                        input
% 1.38/1.00  --splitting_grd                         true
% 1.38/1.00  --splitting_cvd                         false
% 1.38/1.00  --splitting_cvd_svl                     false
% 1.38/1.00  --splitting_nvd                         32
% 1.38/1.00  --sub_typing                            true
% 1.38/1.00  --prep_gs_sim                           true
% 1.38/1.00  --prep_unflatten                        true
% 1.38/1.00  --prep_res_sim                          true
% 1.38/1.00  --prep_upred                            true
% 1.38/1.00  --prep_sem_filter                       exhaustive
% 1.38/1.00  --prep_sem_filter_out                   false
% 1.38/1.00  --pred_elim                             true
% 1.38/1.00  --res_sim_input                         true
% 1.38/1.00  --eq_ax_congr_red                       true
% 1.38/1.00  --pure_diseq_elim                       true
% 1.38/1.00  --brand_transform                       false
% 1.38/1.00  --non_eq_to_eq                          false
% 1.38/1.00  --prep_def_merge                        true
% 1.38/1.00  --prep_def_merge_prop_impl              false
% 1.38/1.00  --prep_def_merge_mbd                    true
% 1.38/1.00  --prep_def_merge_tr_red                 false
% 1.38/1.00  --prep_def_merge_tr_cl                  false
% 1.38/1.00  --smt_preprocessing                     true
% 1.38/1.00  --smt_ac_axioms                         fast
% 1.38/1.00  --preprocessed_out                      false
% 1.38/1.00  --preprocessed_stats                    false
% 1.38/1.00  
% 1.38/1.00  ------ Abstraction refinement Options
% 1.38/1.00  
% 1.38/1.00  --abstr_ref                             []
% 1.38/1.00  --abstr_ref_prep                        false
% 1.38/1.00  --abstr_ref_until_sat                   false
% 1.38/1.00  --abstr_ref_sig_restrict                funpre
% 1.38/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.38/1.00  --abstr_ref_under                       []
% 1.38/1.00  
% 1.38/1.00  ------ SAT Options
% 1.38/1.00  
% 1.38/1.00  --sat_mode                              false
% 1.38/1.00  --sat_fm_restart_options                ""
% 1.38/1.00  --sat_gr_def                            false
% 1.38/1.00  --sat_epr_types                         true
% 1.38/1.00  --sat_non_cyclic_types                  false
% 1.38/1.00  --sat_finite_models                     false
% 1.38/1.00  --sat_fm_lemmas                         false
% 1.38/1.00  --sat_fm_prep                           false
% 1.38/1.00  --sat_fm_uc_incr                        true
% 1.38/1.00  --sat_out_model                         small
% 1.38/1.00  --sat_out_clauses                       false
% 1.38/1.00  
% 1.38/1.00  ------ QBF Options
% 1.38/1.00  
% 1.38/1.00  --qbf_mode                              false
% 1.38/1.00  --qbf_elim_univ                         false
% 1.38/1.00  --qbf_dom_inst                          none
% 1.38/1.00  --qbf_dom_pre_inst                      false
% 1.38/1.00  --qbf_sk_in                             false
% 1.38/1.00  --qbf_pred_elim                         true
% 1.38/1.00  --qbf_split                             512
% 1.38/1.00  
% 1.38/1.00  ------ BMC1 Options
% 1.38/1.00  
% 1.38/1.00  --bmc1_incremental                      false
% 1.38/1.00  --bmc1_axioms                           reachable_all
% 1.38/1.00  --bmc1_min_bound                        0
% 1.38/1.00  --bmc1_max_bound                        -1
% 1.38/1.00  --bmc1_max_bound_default                -1
% 1.38/1.00  --bmc1_symbol_reachability              true
% 1.38/1.00  --bmc1_property_lemmas                  false
% 1.38/1.00  --bmc1_k_induction                      false
% 1.38/1.00  --bmc1_non_equiv_states                 false
% 1.38/1.00  --bmc1_deadlock                         false
% 1.38/1.00  --bmc1_ucm                              false
% 1.38/1.00  --bmc1_add_unsat_core                   none
% 1.38/1.00  --bmc1_unsat_core_children              false
% 1.38/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.38/1.00  --bmc1_out_stat                         full
% 1.38/1.00  --bmc1_ground_init                      false
% 1.38/1.00  --bmc1_pre_inst_next_state              false
% 1.38/1.00  --bmc1_pre_inst_state                   false
% 1.38/1.00  --bmc1_pre_inst_reach_state             false
% 1.38/1.00  --bmc1_out_unsat_core                   false
% 1.38/1.00  --bmc1_aig_witness_out                  false
% 1.38/1.00  --bmc1_verbose                          false
% 1.38/1.00  --bmc1_dump_clauses_tptp                false
% 1.38/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.38/1.00  --bmc1_dump_file                        -
% 1.38/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.38/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.38/1.00  --bmc1_ucm_extend_mode                  1
% 1.38/1.00  --bmc1_ucm_init_mode                    2
% 1.38/1.00  --bmc1_ucm_cone_mode                    none
% 1.38/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.38/1.00  --bmc1_ucm_relax_model                  4
% 1.38/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.38/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.38/1.00  --bmc1_ucm_layered_model                none
% 1.38/1.00  --bmc1_ucm_max_lemma_size               10
% 1.38/1.00  
% 1.38/1.00  ------ AIG Options
% 1.38/1.00  
% 1.38/1.00  --aig_mode                              false
% 1.38/1.00  
% 1.38/1.00  ------ Instantiation Options
% 1.38/1.00  
% 1.38/1.00  --instantiation_flag                    true
% 1.38/1.00  --inst_sos_flag                         false
% 1.38/1.00  --inst_sos_phase                        true
% 1.38/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.38/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.38/1.00  --inst_lit_sel_side                     none
% 1.38/1.00  --inst_solver_per_active                1400
% 1.38/1.00  --inst_solver_calls_frac                1.
% 1.38/1.00  --inst_passive_queue_type               priority_queues
% 1.38/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.38/1.00  --inst_passive_queues_freq              [25;2]
% 1.38/1.00  --inst_dismatching                      true
% 1.38/1.00  --inst_eager_unprocessed_to_passive     true
% 1.38/1.00  --inst_prop_sim_given                   true
% 1.38/1.00  --inst_prop_sim_new                     false
% 1.38/1.00  --inst_subs_new                         false
% 1.38/1.00  --inst_eq_res_simp                      false
% 1.38/1.00  --inst_subs_given                       false
% 1.38/1.00  --inst_orphan_elimination               true
% 1.38/1.00  --inst_learning_loop_flag               true
% 1.38/1.00  --inst_learning_start                   3000
% 1.38/1.00  --inst_learning_factor                  2
% 1.38/1.00  --inst_start_prop_sim_after_learn       3
% 1.38/1.00  --inst_sel_renew                        solver
% 1.38/1.00  --inst_lit_activity_flag                true
% 1.38/1.00  --inst_restr_to_given                   false
% 1.38/1.00  --inst_activity_threshold               500
% 1.38/1.00  --inst_out_proof                        true
% 1.38/1.00  
% 1.38/1.00  ------ Resolution Options
% 1.38/1.00  
% 1.38/1.00  --resolution_flag                       false
% 1.38/1.00  --res_lit_sel                           adaptive
% 1.38/1.00  --res_lit_sel_side                      none
% 1.38/1.00  --res_ordering                          kbo
% 1.38/1.00  --res_to_prop_solver                    active
% 1.38/1.00  --res_prop_simpl_new                    false
% 1.38/1.00  --res_prop_simpl_given                  true
% 1.38/1.00  --res_passive_queue_type                priority_queues
% 1.38/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.38/1.00  --res_passive_queues_freq               [15;5]
% 1.38/1.00  --res_forward_subs                      full
% 1.38/1.00  --res_backward_subs                     full
% 1.38/1.00  --res_forward_subs_resolution           true
% 1.38/1.00  --res_backward_subs_resolution          true
% 1.38/1.00  --res_orphan_elimination                true
% 1.38/1.00  --res_time_limit                        2.
% 1.38/1.00  --res_out_proof                         true
% 1.38/1.00  
% 1.38/1.00  ------ Superposition Options
% 1.38/1.00  
% 1.38/1.00  --superposition_flag                    true
% 1.38/1.00  --sup_passive_queue_type                priority_queues
% 1.38/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.38/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.38/1.00  --demod_completeness_check              fast
% 1.38/1.00  --demod_use_ground                      true
% 1.38/1.00  --sup_to_prop_solver                    passive
% 1.38/1.00  --sup_prop_simpl_new                    true
% 1.38/1.00  --sup_prop_simpl_given                  true
% 1.38/1.00  --sup_fun_splitting                     false
% 1.38/1.00  --sup_smt_interval                      50000
% 1.38/1.00  
% 1.38/1.00  ------ Superposition Simplification Setup
% 1.38/1.00  
% 1.38/1.00  --sup_indices_passive                   []
% 1.38/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.38/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.38/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.38/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.38/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.38/1.00  --sup_full_bw                           [BwDemod]
% 1.38/1.00  --sup_immed_triv                        [TrivRules]
% 1.38/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.38/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.38/1.00  --sup_immed_bw_main                     []
% 1.38/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.38/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.38/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.38/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.38/1.00  
% 1.38/1.00  ------ Combination Options
% 1.38/1.00  
% 1.38/1.00  --comb_res_mult                         3
% 1.38/1.00  --comb_sup_mult                         2
% 1.38/1.00  --comb_inst_mult                        10
% 1.38/1.00  
% 1.38/1.00  ------ Debug Options
% 1.38/1.00  
% 1.38/1.00  --dbg_backtrace                         false
% 1.38/1.00  --dbg_dump_prop_clauses                 false
% 1.38/1.00  --dbg_dump_prop_clauses_file            -
% 1.38/1.00  --dbg_out_stat                          false
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  ------ Proving...
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  % SZS status Theorem for theBenchmark.p
% 1.38/1.00  
% 1.38/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.38/1.00  
% 1.38/1.00  fof(f3,axiom,(
% 1.38/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f38,plain,(
% 1.38/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.38/1.00    inference(cnf_transformation,[],[f3])).
% 1.38/1.00  
% 1.38/1.00  fof(f2,axiom,(
% 1.38/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f37,plain,(
% 1.38/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/1.00    inference(cnf_transformation,[],[f2])).
% 1.38/1.00  
% 1.38/1.00  fof(f7,axiom,(
% 1.38/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f45,plain,(
% 1.38/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.38/1.00    inference(cnf_transformation,[],[f7])).
% 1.38/1.00  
% 1.38/1.00  fof(f56,plain,(
% 1.38/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.38/1.00    inference(definition_unfolding,[],[f37,f45])).
% 1.38/1.00  
% 1.38/1.00  fof(f57,plain,(
% 1.38/1.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 1.38/1.00    inference(definition_unfolding,[],[f38,f56])).
% 1.38/1.00  
% 1.38/1.00  fof(f1,axiom,(
% 1.38/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f15,plain,(
% 1.38/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.38/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 1.38/1.00  
% 1.38/1.00  fof(f17,plain,(
% 1.38/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.38/1.00    inference(ennf_transformation,[],[f15])).
% 1.38/1.00  
% 1.38/1.00  fof(f36,plain,(
% 1.38/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.38/1.00    inference(cnf_transformation,[],[f17])).
% 1.38/1.00  
% 1.38/1.00  fof(f6,axiom,(
% 1.38/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f44,plain,(
% 1.38/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.38/1.00    inference(cnf_transformation,[],[f6])).
% 1.38/1.00  
% 1.38/1.00  fof(f8,axiom,(
% 1.38/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f18,plain,(
% 1.38/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.38/1.00    inference(ennf_transformation,[],[f8])).
% 1.38/1.00  
% 1.38/1.00  fof(f19,plain,(
% 1.38/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.38/1.00    inference(flattening,[],[f18])).
% 1.38/1.00  
% 1.38/1.00  fof(f46,plain,(
% 1.38/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.38/1.00    inference(cnf_transformation,[],[f19])).
% 1.38/1.00  
% 1.38/1.00  fof(f4,axiom,(
% 1.38/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f28,plain,(
% 1.38/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.38/1.00    inference(nnf_transformation,[],[f4])).
% 1.38/1.00  
% 1.38/1.00  fof(f29,plain,(
% 1.38/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.38/1.00    inference(rectify,[],[f28])).
% 1.38/1.00  
% 1.38/1.00  fof(f30,plain,(
% 1.38/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 1.38/1.00    introduced(choice_axiom,[])).
% 1.38/1.00  
% 1.38/1.00  fof(f31,plain,(
% 1.38/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.38/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 1.38/1.00  
% 1.38/1.00  fof(f40,plain,(
% 1.38/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.38/1.00    inference(cnf_transformation,[],[f31])).
% 1.38/1.00  
% 1.38/1.00  fof(f58,plain,(
% 1.38/1.00    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.38/1.00    inference(equality_resolution,[],[f40])).
% 1.38/1.00  
% 1.38/1.00  fof(f5,axiom,(
% 1.38/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f43,plain,(
% 1.38/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.38/1.00    inference(cnf_transformation,[],[f5])).
% 1.38/1.00  
% 1.38/1.00  fof(f13,conjecture,(
% 1.38/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f14,negated_conjecture,(
% 1.38/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.38/1.00    inference(negated_conjecture,[],[f13])).
% 1.38/1.00  
% 1.38/1.00  fof(f16,plain,(
% 1.38/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.38/1.00    inference(pure_predicate_removal,[],[f14])).
% 1.38/1.00  
% 1.38/1.00  fof(f26,plain,(
% 1.38/1.00    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.38/1.00    inference(ennf_transformation,[],[f16])).
% 1.38/1.00  
% 1.38/1.00  fof(f27,plain,(
% 1.38/1.00    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.38/1.00    inference(flattening,[],[f26])).
% 1.38/1.00  
% 1.38/1.00  fof(f34,plain,(
% 1.38/1.00    ( ! [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~m2_connsp_2(k2_struct_0(X0),X0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.38/1.00    introduced(choice_axiom,[])).
% 1.38/1.00  
% 1.38/1.00  fof(f33,plain,(
% 1.38/1.00    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK1),sK1,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.38/1.00    introduced(choice_axiom,[])).
% 1.38/1.00  
% 1.38/1.00  fof(f35,plain,(
% 1.38/1.00    (~m2_connsp_2(k2_struct_0(sK1),sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.38/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f34,f33])).
% 1.38/1.00  
% 1.38/1.00  fof(f54,plain,(
% 1.38/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.38/1.00    inference(cnf_transformation,[],[f35])).
% 1.38/1.00  
% 1.38/1.00  fof(f10,axiom,(
% 1.38/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f21,plain,(
% 1.38/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.38/1.00    inference(ennf_transformation,[],[f10])).
% 1.38/1.00  
% 1.38/1.00  fof(f48,plain,(
% 1.38/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.38/1.00    inference(cnf_transformation,[],[f21])).
% 1.38/1.00  
% 1.38/1.00  fof(f9,axiom,(
% 1.38/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f20,plain,(
% 1.38/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.38/1.00    inference(ennf_transformation,[],[f9])).
% 1.38/1.00  
% 1.38/1.00  fof(f47,plain,(
% 1.38/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.38/1.00    inference(cnf_transformation,[],[f20])).
% 1.38/1.00  
% 1.38/1.00  fof(f53,plain,(
% 1.38/1.00    l1_pre_topc(sK1)),
% 1.38/1.00    inference(cnf_transformation,[],[f35])).
% 1.38/1.00  
% 1.38/1.00  fof(f39,plain,(
% 1.38/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.38/1.00    inference(cnf_transformation,[],[f31])).
% 1.38/1.00  
% 1.38/1.00  fof(f59,plain,(
% 1.38/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.38/1.00    inference(equality_resolution,[],[f39])).
% 1.38/1.00  
% 1.38/1.00  fof(f55,plain,(
% 1.38/1.00    ~m2_connsp_2(k2_struct_0(sK1),sK1,sK2)),
% 1.38/1.00    inference(cnf_transformation,[],[f35])).
% 1.38/1.00  
% 1.38/1.00  fof(f12,axiom,(
% 1.38/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f24,plain,(
% 1.38/1.00    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.38/1.00    inference(ennf_transformation,[],[f12])).
% 1.38/1.00  
% 1.38/1.00  fof(f25,plain,(
% 1.38/1.00    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.38/1.00    inference(flattening,[],[f24])).
% 1.38/1.00  
% 1.38/1.00  fof(f32,plain,(
% 1.38/1.00    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.38/1.00    inference(nnf_transformation,[],[f25])).
% 1.38/1.00  
% 1.38/1.00  fof(f51,plain,(
% 1.38/1.00    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.38/1.00    inference(cnf_transformation,[],[f32])).
% 1.38/1.00  
% 1.38/1.00  fof(f52,plain,(
% 1.38/1.00    v2_pre_topc(sK1)),
% 1.38/1.00    inference(cnf_transformation,[],[f35])).
% 1.38/1.00  
% 1.38/1.00  fof(f11,axiom,(
% 1.38/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.38/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.38/1.00  
% 1.38/1.00  fof(f22,plain,(
% 1.38/1.00    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.38/1.00    inference(ennf_transformation,[],[f11])).
% 1.38/1.00  
% 1.38/1.00  fof(f23,plain,(
% 1.38/1.00    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.38/1.00    inference(flattening,[],[f22])).
% 1.38/1.00  
% 1.38/1.00  fof(f49,plain,(
% 1.38/1.00    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.38/1.00    inference(cnf_transformation,[],[f23])).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1,plain,
% 1.38/1.00      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 1.38/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_0,plain,
% 1.38/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.38/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_7,plain,
% 1.38/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.38/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_8,plain,
% 1.38/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.38/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_362,plain,
% 1.38/1.00      ( r2_hidden(X0,X1)
% 1.38/1.00      | v1_xboole_0(X1)
% 1.38/1.00      | k2_subset_1(X2) != X0
% 1.38/1.00      | k1_zfmisc_1(X2) != X1 ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_8]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_363,plain,
% 1.38/1.00      ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0))
% 1.38/1.00      | v1_xboole_0(k1_zfmisc_1(X0)) ),
% 1.38/1.00      inference(unflattening,[status(thm)],[c_362]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_424,plain,
% 1.38/1.00      ( ~ r2_hidden(X0,X1)
% 1.38/1.00      | r2_hidden(k2_subset_1(X2),k1_zfmisc_1(X2))
% 1.38/1.00      | k1_zfmisc_1(X2) != X1 ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_363]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_425,plain,
% 1.38/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 1.38/1.00      | r2_hidden(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
% 1.38/1.00      inference(unflattening,[status(thm)],[c_424]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_4,plain,
% 1.38/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.38/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_659,plain,
% 1.38/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.38/1.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_683,plain,
% 1.38/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
% 1.38/1.00      inference(bin_hyper_res,[status(thm)],[c_425,c_659]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_748,plain,
% 1.38/1.00      ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0))
% 1.38/1.00      | X0 != X1
% 1.38/1.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) != X3 ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_683]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_749,plain,
% 1.38/1.00      ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.38/1.00      inference(unflattening,[status(thm)],[c_748]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1320,plain,
% 1.38/1.00      ( r2_hidden(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.38/1.00      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_6,plain,
% 1.38/1.00      ( k2_subset_1(X0) = X0 ),
% 1.38/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1333,plain,
% 1.38/1.00      ( r2_hidden(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.38/1.00      inference(light_normalisation,[status(thm)],[c_1320,c_6]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_15,negated_conjecture,
% 1.38/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.38/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_388,plain,
% 1.38/1.00      ( r2_hidden(X0,X1)
% 1.38/1.00      | v1_xboole_0(X1)
% 1.38/1.00      | k1_zfmisc_1(u1_struct_0(sK1)) != X1
% 1.38/1.00      | sK2 != X0 ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_389,plain,
% 1.38/1.00      ( r2_hidden(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.38/1.00      inference(unflattening,[status(thm)],[c_388]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_436,plain,
% 1.38/1.00      ( ~ r2_hidden(X0,X1)
% 1.38/1.00      | r2_hidden(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_389]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_437,plain,
% 1.38/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | r2_hidden(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.38/1.00      inference(unflattening,[status(thm)],[c_436]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1322,plain,
% 1.38/1.00      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.38/1.00      | r2_hidden(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.38/1.00      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_10,plain,
% 1.38/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.38/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_9,plain,
% 1.38/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.38/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_242,plain,
% 1.38/1.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.38/1.00      inference(resolution,[status(thm)],[c_10,c_9]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_16,negated_conjecture,
% 1.38/1.00      ( l1_pre_topc(sK1) ),
% 1.38/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_338,plain,
% 1.38/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_242,c_16]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_339,plain,
% 1.38/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.38/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1353,plain,
% 1.38/1.00      ( r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.38/1.00      | r2_hidden(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 1.38/1.00      inference(light_normalisation,[status(thm)],[c_1322,c_339]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1533,plain,
% 1.38/1.00      ( r2_hidden(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 1.38/1.00      inference(superposition,[status(thm)],[c_1333,c_1353]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_5,plain,
% 1.38/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.38/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1506,plain,
% 1.38/1.00      ( r1_tarski(sK2,k2_struct_0(sK1))
% 1.38/1.00      | ~ r2_hidden(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
% 1.38/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1507,plain,
% 1.38/1.00      ( r1_tarski(sK2,k2_struct_0(sK1)) = iProver_top
% 1.38/1.00      | r2_hidden(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.38/1.00      inference(predicate_to_equality,[status(thm)],[c_1506]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_14,negated_conjecture,
% 1.38/1.00      ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2) ),
% 1.38/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_12,plain,
% 1.38/1.00      ( m2_connsp_2(X0,X1,X2)
% 1.38/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.38/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.38/1.00      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.38/1.00      | ~ v2_pre_topc(X1)
% 1.38/1.00      | ~ l1_pre_topc(X1) ),
% 1.38/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_17,negated_conjecture,
% 1.38/1.00      ( v2_pre_topc(sK1) ),
% 1.38/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_295,plain,
% 1.38/1.00      ( m2_connsp_2(X0,X1,X2)
% 1.38/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.38/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.38/1.00      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 1.38/1.00      | ~ l1_pre_topc(X1)
% 1.38/1.00      | sK1 != X1 ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_296,plain,
% 1.38/1.00      ( m2_connsp_2(X0,sK1,X1)
% 1.38/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 1.38/1.00      | ~ l1_pre_topc(sK1) ),
% 1.38/1.00      inference(unflattening,[status(thm)],[c_295]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_300,plain,
% 1.38/1.00      ( ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 1.38/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | m2_connsp_2(X0,sK1,X1) ),
% 1.38/1.00      inference(global_propositional_subsumption,
% 1.38/1.00                [status(thm)],
% 1.38/1.00                [c_296,c_16]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_301,plain,
% 1.38/1.00      ( m2_connsp_2(X0,sK1,X1)
% 1.38/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ r1_tarski(X1,k1_tops_1(sK1,X0)) ),
% 1.38/1.00      inference(renaming,[status(thm)],[c_300]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_345,plain,
% 1.38/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 1.38/1.00      | k2_struct_0(sK1) != X0
% 1.38/1.00      | sK2 != X1
% 1.38/1.00      | sK1 != sK1 ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_301]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_346,plain,
% 1.38/1.00      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
% 1.38/1.00      inference(unflattening,[status(thm)],[c_345]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_348,plain,
% 1.38/1.00      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.38/1.00      | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
% 1.38/1.00      inference(global_propositional_subsumption,
% 1.38/1.00                [status(thm)],
% 1.38/1.00                [c_346,c_15]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_374,plain,
% 1.38/1.00      ( ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1)))
% 1.38/1.00      | k2_subset_1(X0) != k2_struct_0(sK1)
% 1.38/1.00      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0) ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_348]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1323,plain,
% 1.38/1.00      ( k2_subset_1(X0) != k2_struct_0(sK1)
% 1.38/1.00      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
% 1.38/1.00      | r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) != iProver_top ),
% 1.38/1.00      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_11,plain,
% 1.38/1.00      ( ~ v2_pre_topc(X0)
% 1.38/1.00      | ~ l1_pre_topc(X0)
% 1.38/1.00      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 1.38/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_319,plain,
% 1.38/1.00      ( ~ l1_pre_topc(X0)
% 1.38/1.00      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 1.38/1.00      | sK1 != X0 ),
% 1.38/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_320,plain,
% 1.38/1.00      ( ~ l1_pre_topc(sK1)
% 1.38/1.00      | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 1.38/1.00      inference(unflattening,[status(thm)],[c_319]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_29,plain,
% 1.38/1.00      ( ~ v2_pre_topc(sK1)
% 1.38/1.00      | ~ l1_pre_topc(sK1)
% 1.38/1.00      | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 1.38/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_322,plain,
% 1.38/1.00      ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 1.38/1.00      inference(global_propositional_subsumption,
% 1.38/1.00                [status(thm)],
% 1.38/1.00                [c_320,c_17,c_16,c_29]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1370,plain,
% 1.38/1.00      ( k2_struct_0(sK1) != X0
% 1.38/1.00      | k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0)
% 1.38/1.00      | r1_tarski(sK2,k2_struct_0(sK1)) != iProver_top ),
% 1.38/1.00      inference(light_normalisation,
% 1.38/1.00                [status(thm)],
% 1.38/1.00                [c_1323,c_6,c_322,c_339]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1474,plain,
% 1.38/1.00      ( k2_struct_0(sK1) != k2_struct_0(sK1)
% 1.38/1.00      | r1_tarski(sK2,k2_struct_0(sK1)) != iProver_top ),
% 1.38/1.00      inference(equality_resolution,[status(thm)],[c_1370]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1055,plain,( X0 = X0 ),theory(equality) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1074,plain,
% 1.38/1.00      ( sK1 = sK1 ),
% 1.38/1.00      inference(instantiation,[status(thm)],[c_1055]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1062,plain,
% 1.38/1.00      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 1.38/1.00      theory(equality) ).
% 1.38/1.00  
% 1.38/1.00  cnf(c_1070,plain,
% 1.38/1.00      ( k2_struct_0(sK1) = k2_struct_0(sK1) | sK1 != sK1 ),
% 1.38/1.00      inference(instantiation,[status(thm)],[c_1062]) ).
% 1.38/1.00  
% 1.38/1.00  cnf(contradiction,plain,
% 1.38/1.00      ( $false ),
% 1.38/1.00      inference(minisat,
% 1.38/1.00                [status(thm)],
% 1.38/1.00                [c_1533,c_1507,c_1474,c_1074,c_1070]) ).
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.38/1.00  
% 1.38/1.00  ------                               Statistics
% 1.38/1.00  
% 1.38/1.00  ------ General
% 1.38/1.00  
% 1.38/1.00  abstr_ref_over_cycles:                  0
% 1.38/1.00  abstr_ref_under_cycles:                 0
% 1.38/1.00  gc_basic_clause_elim:                   0
% 1.38/1.00  forced_gc_time:                         0
% 1.38/1.00  parsing_time:                           0.008
% 1.38/1.00  unif_index_cands_time:                  0.
% 1.38/1.00  unif_index_add_time:                    0.
% 1.38/1.00  orderings_time:                         0.
% 1.38/1.00  out_proof_time:                         0.012
% 1.38/1.00  total_time:                             0.072
% 1.38/1.00  num_of_symbols:                         50
% 1.38/1.00  num_of_terms:                           817
% 1.38/1.00  
% 1.38/1.00  ------ Preprocessing
% 1.38/1.00  
% 1.38/1.00  num_of_splits:                          0
% 1.38/1.00  num_of_split_atoms:                     0
% 1.38/1.00  num_of_reused_defs:                     0
% 1.38/1.00  num_eq_ax_congr_red:                    21
% 1.38/1.00  num_of_sem_filtered_clauses:            1
% 1.38/1.00  num_of_subtypes:                        0
% 1.38/1.00  monotx_restored_types:                  0
% 1.38/1.00  sat_num_of_epr_types:                   0
% 1.38/1.00  sat_num_of_non_cyclic_types:            0
% 1.38/1.00  sat_guarded_non_collapsed_types:        0
% 1.38/1.00  num_pure_diseq_elim:                    0
% 1.38/1.00  simp_replaced_by:                       0
% 1.38/1.00  res_preprocessed:                       75
% 1.38/1.00  prep_upred:                             0
% 1.38/1.00  prep_unflattend:                        61
% 1.38/1.00  smt_new_axioms:                         0
% 1.38/1.00  pred_elim_cands:                        2
% 1.38/1.00  pred_elim:                              6
% 1.38/1.00  pred_elim_cl:                           6
% 1.38/1.00  pred_elim_cycles:                       10
% 1.38/1.00  merged_defs:                            8
% 1.38/1.00  merged_defs_ncl:                        0
% 1.38/1.00  bin_hyper_res:                          9
% 1.38/1.00  prep_cycles:                            4
% 1.38/1.00  pred_elim_time:                         0.011
% 1.38/1.00  splitting_time:                         0.
% 1.38/1.00  sem_filter_time:                        0.
% 1.38/1.00  monotx_time:                            0.
% 1.38/1.00  subtype_inf_time:                       0.
% 1.38/1.00  
% 1.38/1.00  ------ Problem properties
% 1.38/1.00  
% 1.38/1.00  clauses:                                12
% 1.38/1.00  conjectures:                            0
% 1.38/1.00  epr:                                    0
% 1.38/1.00  horn:                                   11
% 1.38/1.00  ground:                                 3
% 1.38/1.00  unary:                                  5
% 1.38/1.00  binary:                                 4
% 1.38/1.00  lits:                                   22
% 1.38/1.00  lits_eq:                                8
% 1.38/1.00  fd_pure:                                0
% 1.38/1.00  fd_pseudo:                              0
% 1.38/1.00  fd_cond:                                0
% 1.38/1.00  fd_pseudo_cond:                         2
% 1.38/1.00  ac_symbols:                             0
% 1.38/1.00  
% 1.38/1.00  ------ Propositional Solver
% 1.38/1.00  
% 1.38/1.00  prop_solver_calls:                      24
% 1.38/1.00  prop_fast_solver_calls:                 466
% 1.38/1.00  smt_solver_calls:                       0
% 1.38/1.00  smt_fast_solver_calls:                  0
% 1.38/1.00  prop_num_of_clauses:                    264
% 1.38/1.00  prop_preprocess_simplified:             2087
% 1.38/1.00  prop_fo_subsumed:                       4
% 1.38/1.00  prop_solver_time:                       0.
% 1.38/1.00  smt_solver_time:                        0.
% 1.38/1.00  smt_fast_solver_time:                   0.
% 1.38/1.00  prop_fast_solver_time:                  0.
% 1.38/1.00  prop_unsat_core_time:                   0.
% 1.38/1.00  
% 1.38/1.00  ------ QBF
% 1.38/1.00  
% 1.38/1.00  qbf_q_res:                              0
% 1.38/1.00  qbf_num_tautologies:                    0
% 1.38/1.00  qbf_prep_cycles:                        0
% 1.38/1.00  
% 1.38/1.00  ------ BMC1
% 1.38/1.00  
% 1.38/1.00  bmc1_current_bound:                     -1
% 1.38/1.00  bmc1_last_solved_bound:                 -1
% 1.38/1.00  bmc1_unsat_core_size:                   -1
% 1.38/1.00  bmc1_unsat_core_parents_size:           -1
% 1.38/1.00  bmc1_merge_next_fun:                    0
% 1.38/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.38/1.00  
% 1.38/1.00  ------ Instantiation
% 1.38/1.00  
% 1.38/1.00  inst_num_of_clauses:                    57
% 1.38/1.00  inst_num_in_passive:                    11
% 1.38/1.00  inst_num_in_active:                     36
% 1.38/1.00  inst_num_in_unprocessed:                10
% 1.38/1.00  inst_num_of_loops:                      40
% 1.38/1.00  inst_num_of_learning_restarts:          0
% 1.38/1.00  inst_num_moves_active_passive:          2
% 1.38/1.00  inst_lit_activity:                      0
% 1.38/1.00  inst_lit_activity_moves:                0
% 1.38/1.00  inst_num_tautologies:                   0
% 1.38/1.00  inst_num_prop_implied:                  0
% 1.38/1.00  inst_num_existing_simplified:           0
% 1.38/1.00  inst_num_eq_res_simplified:             0
% 1.38/1.00  inst_num_child_elim:                    0
% 1.38/1.00  inst_num_of_dismatching_blockings:      5
% 1.38/1.00  inst_num_of_non_proper_insts:           28
% 1.38/1.00  inst_num_of_duplicates:                 0
% 1.38/1.00  inst_inst_num_from_inst_to_res:         0
% 1.38/1.00  inst_dismatching_checking_time:         0.
% 1.38/1.00  
% 1.38/1.00  ------ Resolution
% 1.38/1.00  
% 1.38/1.00  res_num_of_clauses:                     0
% 1.38/1.00  res_num_in_passive:                     0
% 1.38/1.00  res_num_in_active:                      0
% 1.38/1.00  res_num_of_loops:                       79
% 1.38/1.00  res_forward_subset_subsumed:            4
% 1.38/1.00  res_backward_subset_subsumed:           0
% 1.38/1.00  res_forward_subsumed:                   0
% 1.38/1.00  res_backward_subsumed:                  2
% 1.38/1.00  res_forward_subsumption_resolution:     0
% 1.38/1.00  res_backward_subsumption_resolution:    0
% 1.38/1.00  res_clause_to_clause_subsumption:       41
% 1.38/1.00  res_orphan_elimination:                 0
% 1.38/1.00  res_tautology_del:                      24
% 1.38/1.00  res_num_eq_res_simplified:              1
% 1.38/1.00  res_num_sel_changes:                    0
% 1.38/1.00  res_moves_from_active_to_pass:          0
% 1.38/1.00  
% 1.38/1.00  ------ Superposition
% 1.38/1.00  
% 1.38/1.00  sup_time_total:                         0.
% 1.38/1.00  sup_time_generating:                    0.
% 1.38/1.00  sup_time_sim_full:                      0.
% 1.38/1.00  sup_time_sim_immed:                     0.
% 1.38/1.00  
% 1.38/1.00  sup_num_of_clauses:                     14
% 1.38/1.00  sup_num_in_active:                      8
% 1.38/1.00  sup_num_in_passive:                     6
% 1.38/1.00  sup_num_of_loops:                       7
% 1.38/1.00  sup_fw_superposition:                   0
% 1.38/1.00  sup_bw_superposition:                   1
% 1.38/1.00  sup_immediate_simplified:               0
% 1.38/1.00  sup_given_eliminated:                   0
% 1.38/1.00  comparisons_done:                       0
% 1.38/1.00  comparisons_avoided:                    0
% 1.38/1.00  
% 1.38/1.00  ------ Simplifications
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  sim_fw_subset_subsumed:                 0
% 1.38/1.00  sim_bw_subset_subsumed:                 0
% 1.38/1.00  sim_fw_subsumed:                        0
% 1.38/1.00  sim_bw_subsumed:                        0
% 1.38/1.00  sim_fw_subsumption_res:                 0
% 1.38/1.00  sim_bw_subsumption_res:                 0
% 1.38/1.00  sim_tautology_del:                      0
% 1.38/1.00  sim_eq_tautology_del:                   0
% 1.38/1.00  sim_eq_res_simp:                        1
% 1.38/1.00  sim_fw_demodulated:                     0
% 1.38/1.00  sim_bw_demodulated:                     0
% 1.38/1.00  sim_light_normalised:                   4
% 1.38/1.00  sim_joinable_taut:                      0
% 1.38/1.00  sim_joinable_simp:                      0
% 1.38/1.00  sim_ac_normalised:                      0
% 1.38/1.00  sim_smt_subsumption:                    0
% 1.38/1.00  
%------------------------------------------------------------------------------

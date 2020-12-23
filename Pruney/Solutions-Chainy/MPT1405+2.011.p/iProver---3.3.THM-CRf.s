%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:49 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 205 expanded)
%              Number of clauses        :   57 (  67 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   22
%              Number of atoms          :  321 ( 712 expanded)
%              Number of equality atoms :   41 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f22,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m2_connsp_2(k2_struct_0(X0),X0,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK4),sK4,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK4),sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f38,f56,f55])).

fof(f91,plain,(
    ~ m2_connsp_2(k2_struct_0(sK4),sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f83,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2393,plain,
    ( r1_tarski(k2_struct_0(sK4),X0)
    | ~ r2_hidden(sK1(k2_struct_0(sK4),X0),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3278,plain,
    ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4))
    | ~ r2_hidden(sK1(k2_struct_0(sK4),k2_struct_0(sK4)),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2393])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2394,plain,
    ( r1_tarski(k2_struct_0(sK4),X0)
    | r2_hidden(sK1(k2_struct_0(sK4),X0),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2991,plain,
    ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4))
    | r2_hidden(sK1(k2_struct_0(sK4),k2_struct_0(sK4)),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2394])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_279,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_280,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_279])).

cnf(c_746,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X2,X3)
    | v1_xboole_0(X3)
    | X0 != X2
    | k1_zfmisc_1(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_280])).

cnf(c_747,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_757,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_747,c_20])).

cnf(c_1063,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_757])).

cnf(c_1905,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_18,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_200,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_1])).

cnf(c_201,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_30,negated_conjecture,
    ( ~ m2_connsp_2(k2_struct_0(sK4),sK4,sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_26,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_500,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_501,plain,
    ( m2_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,k1_tops_1(sK4,X0))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_505,plain,
    ( ~ r1_tarski(X1,k1_tops_1(sK4,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m2_connsp_2(X0,sK4,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_32])).

cnf(c_506,plain,
    ( m2_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,k1_tops_1(sK4,X0)) ),
    inference(renaming,[status(thm)],[c_505])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,k1_tops_1(sK4,X0))
    | k2_struct_0(sK4) != X0
    | sK5 != X1
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_506])).

cnf(c_561,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_563,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_31])).

cnf(c_791,plain,
    ( ~ r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4)))
    | ~ r2_hidden(X0,X1)
    | k2_struct_0(sK4) != X0
    | k1_zfmisc_1(u1_struct_0(sK4)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_563])).

cnf(c_792,plain,
    ( ~ r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4)))
    | ~ r2_hidden(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_791])).

cnf(c_1902,plain,
    ( r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4))) != iProver_top
    | r2_hidden(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_25,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_468,plain,
    ( ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_469,plain,
    ( ~ l1_pre_topc(sK4)
    | k1_tops_1(sK4,k2_struct_0(sK4)) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_471,plain,
    ( k1_tops_1(sK4,k2_struct_0(sK4)) = k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_32])).

cnf(c_24,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_454,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_24,c_23])).

cnf(c_535,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_454,c_32])).

cnf(c_536,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_2012,plain,
    ( r1_tarski(sK5,k2_struct_0(sK4)) != iProver_top
    | r2_hidden(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1902,c_471,c_536])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_277,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_804,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_278,c_31])).

cnf(c_805,plain,
    ( r1_tarski(sK5,X0)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_1901,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_1956,plain,
    ( k1_zfmisc_1(k2_struct_0(sK4)) != k1_zfmisc_1(X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1901,c_536])).

cnf(c_2162,plain,
    ( r1_tarski(sK5,k2_struct_0(sK4)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1956])).

cnf(c_2432,plain,
    ( r2_hidden(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2012,c_2162])).

cnf(c_2437,plain,
    ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_2432])).

cnf(c_2438,plain,
    ( ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3278,c_2991,c_2438])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.82/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/0.99  
% 2.82/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/0.99  
% 2.82/0.99  ------  iProver source info
% 2.82/0.99  
% 2.82/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.82/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/0.99  git: non_committed_changes: false
% 2.82/0.99  git: last_make_outside_of_git: false
% 2.82/0.99  
% 2.82/0.99  ------ 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options
% 2.82/0.99  
% 2.82/0.99  --out_options                           all
% 2.82/0.99  --tptp_safe_out                         true
% 2.82/0.99  --problem_path                          ""
% 2.82/0.99  --include_path                          ""
% 2.82/0.99  --clausifier                            res/vclausify_rel
% 2.82/0.99  --clausifier_options                    --mode clausify
% 2.82/0.99  --stdin                                 false
% 2.82/0.99  --stats_out                             all
% 2.82/0.99  
% 2.82/0.99  ------ General Options
% 2.82/0.99  
% 2.82/0.99  --fof                                   false
% 2.82/0.99  --time_out_real                         305.
% 2.82/0.99  --time_out_virtual                      -1.
% 2.82/0.99  --symbol_type_check                     false
% 2.82/0.99  --clausify_out                          false
% 2.82/0.99  --sig_cnt_out                           false
% 2.82/0.99  --trig_cnt_out                          false
% 2.82/0.99  --trig_cnt_out_tolerance                1.
% 2.82/0.99  --trig_cnt_out_sk_spl                   false
% 2.82/0.99  --abstr_cl_out                          false
% 2.82/0.99  
% 2.82/0.99  ------ Global Options
% 2.82/0.99  
% 2.82/0.99  --schedule                              default
% 2.82/0.99  --add_important_lit                     false
% 2.82/0.99  --prop_solver_per_cl                    1000
% 2.82/0.99  --min_unsat_core                        false
% 2.82/0.99  --soft_assumptions                      false
% 2.82/0.99  --soft_lemma_size                       3
% 2.82/0.99  --prop_impl_unit_size                   0
% 2.82/0.99  --prop_impl_unit                        []
% 2.82/0.99  --share_sel_clauses                     true
% 2.82/0.99  --reset_solvers                         false
% 2.82/0.99  --bc_imp_inh                            [conj_cone]
% 2.82/0.99  --conj_cone_tolerance                   3.
% 2.82/0.99  --extra_neg_conj                        none
% 2.82/0.99  --large_theory_mode                     true
% 2.82/0.99  --prolific_symb_bound                   200
% 2.82/0.99  --lt_threshold                          2000
% 2.82/0.99  --clause_weak_htbl                      true
% 2.82/0.99  --gc_record_bc_elim                     false
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing Options
% 2.82/0.99  
% 2.82/0.99  --preprocessing_flag                    true
% 2.82/0.99  --time_out_prep_mult                    0.1
% 2.82/0.99  --splitting_mode                        input
% 2.82/0.99  --splitting_grd                         true
% 2.82/0.99  --splitting_cvd                         false
% 2.82/0.99  --splitting_cvd_svl                     false
% 2.82/0.99  --splitting_nvd                         32
% 2.82/0.99  --sub_typing                            true
% 2.82/0.99  --prep_gs_sim                           true
% 2.82/0.99  --prep_unflatten                        true
% 2.82/0.99  --prep_res_sim                          true
% 2.82/0.99  --prep_upred                            true
% 2.82/0.99  --prep_sem_filter                       exhaustive
% 2.82/0.99  --prep_sem_filter_out                   false
% 2.82/0.99  --pred_elim                             true
% 2.82/0.99  --res_sim_input                         true
% 2.82/0.99  --eq_ax_congr_red                       true
% 2.82/0.99  --pure_diseq_elim                       true
% 2.82/0.99  --brand_transform                       false
% 2.82/0.99  --non_eq_to_eq                          false
% 2.82/0.99  --prep_def_merge                        true
% 2.82/0.99  --prep_def_merge_prop_impl              false
% 2.82/0.99  --prep_def_merge_mbd                    true
% 2.82/0.99  --prep_def_merge_tr_red                 false
% 2.82/0.99  --prep_def_merge_tr_cl                  false
% 2.82/0.99  --smt_preprocessing                     true
% 2.82/0.99  --smt_ac_axioms                         fast
% 2.82/0.99  --preprocessed_out                      false
% 2.82/0.99  --preprocessed_stats                    false
% 2.82/0.99  
% 2.82/0.99  ------ Abstraction refinement Options
% 2.82/0.99  
% 2.82/0.99  --abstr_ref                             []
% 2.82/0.99  --abstr_ref_prep                        false
% 2.82/0.99  --abstr_ref_until_sat                   false
% 2.82/0.99  --abstr_ref_sig_restrict                funpre
% 2.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.99  --abstr_ref_under                       []
% 2.82/0.99  
% 2.82/0.99  ------ SAT Options
% 2.82/0.99  
% 2.82/0.99  --sat_mode                              false
% 2.82/0.99  --sat_fm_restart_options                ""
% 2.82/0.99  --sat_gr_def                            false
% 2.82/0.99  --sat_epr_types                         true
% 2.82/0.99  --sat_non_cyclic_types                  false
% 2.82/0.99  --sat_finite_models                     false
% 2.82/0.99  --sat_fm_lemmas                         false
% 2.82/0.99  --sat_fm_prep                           false
% 2.82/0.99  --sat_fm_uc_incr                        true
% 2.82/0.99  --sat_out_model                         small
% 2.82/0.99  --sat_out_clauses                       false
% 2.82/0.99  
% 2.82/0.99  ------ QBF Options
% 2.82/0.99  
% 2.82/0.99  --qbf_mode                              false
% 2.82/0.99  --qbf_elim_univ                         false
% 2.82/0.99  --qbf_dom_inst                          none
% 2.82/0.99  --qbf_dom_pre_inst                      false
% 2.82/0.99  --qbf_sk_in                             false
% 2.82/0.99  --qbf_pred_elim                         true
% 2.82/0.99  --qbf_split                             512
% 2.82/0.99  
% 2.82/0.99  ------ BMC1 Options
% 2.82/0.99  
% 2.82/0.99  --bmc1_incremental                      false
% 2.82/0.99  --bmc1_axioms                           reachable_all
% 2.82/0.99  --bmc1_min_bound                        0
% 2.82/0.99  --bmc1_max_bound                        -1
% 2.82/0.99  --bmc1_max_bound_default                -1
% 2.82/0.99  --bmc1_symbol_reachability              true
% 2.82/0.99  --bmc1_property_lemmas                  false
% 2.82/0.99  --bmc1_k_induction                      false
% 2.82/0.99  --bmc1_non_equiv_states                 false
% 2.82/0.99  --bmc1_deadlock                         false
% 2.82/0.99  --bmc1_ucm                              false
% 2.82/0.99  --bmc1_add_unsat_core                   none
% 2.82/0.99  --bmc1_unsat_core_children              false
% 2.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.99  --bmc1_out_stat                         full
% 2.82/0.99  --bmc1_ground_init                      false
% 2.82/0.99  --bmc1_pre_inst_next_state              false
% 2.82/0.99  --bmc1_pre_inst_state                   false
% 2.82/0.99  --bmc1_pre_inst_reach_state             false
% 2.82/0.99  --bmc1_out_unsat_core                   false
% 2.82/0.99  --bmc1_aig_witness_out                  false
% 2.82/0.99  --bmc1_verbose                          false
% 2.82/0.99  --bmc1_dump_clauses_tptp                false
% 2.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.99  --bmc1_dump_file                        -
% 2.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.99  --bmc1_ucm_extend_mode                  1
% 2.82/0.99  --bmc1_ucm_init_mode                    2
% 2.82/0.99  --bmc1_ucm_cone_mode                    none
% 2.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.99  --bmc1_ucm_relax_model                  4
% 2.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.99  --bmc1_ucm_layered_model                none
% 2.82/0.99  --bmc1_ucm_max_lemma_size               10
% 2.82/0.99  
% 2.82/0.99  ------ AIG Options
% 2.82/0.99  
% 2.82/0.99  --aig_mode                              false
% 2.82/0.99  
% 2.82/0.99  ------ Instantiation Options
% 2.82/0.99  
% 2.82/0.99  --instantiation_flag                    true
% 2.82/0.99  --inst_sos_flag                         false
% 2.82/0.99  --inst_sos_phase                        true
% 2.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.99  --inst_lit_sel_side                     num_symb
% 2.82/0.99  --inst_solver_per_active                1400
% 2.82/0.99  --inst_solver_calls_frac                1.
% 2.82/0.99  --inst_passive_queue_type               priority_queues
% 2.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/0.99  --inst_passive_queues_freq              [25;2]
% 2.82/0.99  --inst_dismatching                      true
% 2.82/0.99  --inst_eager_unprocessed_to_passive     true
% 2.82/0.99  --inst_prop_sim_given                   true
% 2.82/0.99  --inst_prop_sim_new                     false
% 2.82/0.99  --inst_subs_new                         false
% 2.82/0.99  --inst_eq_res_simp                      false
% 2.82/0.99  --inst_subs_given                       false
% 2.82/0.99  --inst_orphan_elimination               true
% 2.82/0.99  --inst_learning_loop_flag               true
% 2.82/0.99  --inst_learning_start                   3000
% 2.82/0.99  --inst_learning_factor                  2
% 2.82/0.99  --inst_start_prop_sim_after_learn       3
% 2.82/0.99  --inst_sel_renew                        solver
% 2.82/0.99  --inst_lit_activity_flag                true
% 2.82/0.99  --inst_restr_to_given                   false
% 2.82/0.99  --inst_activity_threshold               500
% 2.82/0.99  --inst_out_proof                        true
% 2.82/0.99  
% 2.82/0.99  ------ Resolution Options
% 2.82/0.99  
% 2.82/0.99  --resolution_flag                       true
% 2.82/0.99  --res_lit_sel                           adaptive
% 2.82/0.99  --res_lit_sel_side                      none
% 2.82/0.99  --res_ordering                          kbo
% 2.82/0.99  --res_to_prop_solver                    active
% 2.82/0.99  --res_prop_simpl_new                    false
% 2.82/0.99  --res_prop_simpl_given                  true
% 2.82/0.99  --res_passive_queue_type                priority_queues
% 2.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/0.99  --res_passive_queues_freq               [15;5]
% 2.82/0.99  --res_forward_subs                      full
% 2.82/0.99  --res_backward_subs                     full
% 2.82/0.99  --res_forward_subs_resolution           true
% 2.82/0.99  --res_backward_subs_resolution          true
% 2.82/0.99  --res_orphan_elimination                true
% 2.82/0.99  --res_time_limit                        2.
% 2.82/0.99  --res_out_proof                         true
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Options
% 2.82/0.99  
% 2.82/0.99  --superposition_flag                    true
% 2.82/0.99  --sup_passive_queue_type                priority_queues
% 2.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.99  --demod_completeness_check              fast
% 2.82/0.99  --demod_use_ground                      true
% 2.82/0.99  --sup_to_prop_solver                    passive
% 2.82/0.99  --sup_prop_simpl_new                    true
% 2.82/0.99  --sup_prop_simpl_given                  true
% 2.82/0.99  --sup_fun_splitting                     false
% 2.82/0.99  --sup_smt_interval                      50000
% 2.82/0.99  
% 2.82/0.99  ------ Superposition Simplification Setup
% 2.82/0.99  
% 2.82/0.99  --sup_indices_passive                   []
% 2.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_full_bw                           [BwDemod]
% 2.82/0.99  --sup_immed_triv                        [TrivRules]
% 2.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_immed_bw_main                     []
% 2.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.99  
% 2.82/0.99  ------ Combination Options
% 2.82/0.99  
% 2.82/0.99  --comb_res_mult                         3
% 2.82/0.99  --comb_sup_mult                         2
% 2.82/0.99  --comb_inst_mult                        10
% 2.82/0.99  
% 2.82/0.99  ------ Debug Options
% 2.82/0.99  
% 2.82/0.99  --dbg_backtrace                         false
% 2.82/0.99  --dbg_dump_prop_clauses                 false
% 2.82/0.99  --dbg_dump_prop_clauses_file            -
% 2.82/0.99  --dbg_out_stat                          false
% 2.82/0.99  ------ Parsing...
% 2.82/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/0.99  
% 2.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/0.99  ------ Proving...
% 2.82/0.99  ------ Problem Properties 
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  clauses                                 30
% 2.82/0.99  conjectures                             0
% 2.82/0.99  EPR                                     5
% 2.82/0.99  Horn                                    26
% 2.82/0.99  unary                                   9
% 2.82/0.99  binary                                  17
% 2.82/0.99  lits                                    56
% 2.82/0.99  lits eq                                 14
% 2.82/0.99  fd_pure                                 0
% 2.82/0.99  fd_pseudo                               0
% 2.82/0.99  fd_cond                                 1
% 2.82/0.99  fd_pseudo_cond                          1
% 2.82/0.99  AC symbols                              0
% 2.82/0.99  
% 2.82/0.99  ------ Schedule dynamic 5 is on 
% 2.82/0.99  
% 2.82/0.99  ------ no conjectures: strip conj schedule 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.82/0.99  
% 2.82/0.99  
% 2.82/0.99  ------ 
% 2.82/0.99  Current options:
% 2.82/0.99  ------ 
% 2.82/0.99  
% 2.82/0.99  ------ Input Options
% 2.82/0.99  
% 2.82/0.99  --out_options                           all
% 2.82/0.99  --tptp_safe_out                         true
% 2.82/0.99  --problem_path                          ""
% 2.82/0.99  --include_path                          ""
% 2.82/0.99  --clausifier                            res/vclausify_rel
% 2.82/0.99  --clausifier_options                    --mode clausify
% 2.82/0.99  --stdin                                 false
% 2.82/0.99  --stats_out                             all
% 2.82/0.99  
% 2.82/0.99  ------ General Options
% 2.82/0.99  
% 2.82/0.99  --fof                                   false
% 2.82/0.99  --time_out_real                         305.
% 2.82/0.99  --time_out_virtual                      -1.
% 2.82/0.99  --symbol_type_check                     false
% 2.82/0.99  --clausify_out                          false
% 2.82/0.99  --sig_cnt_out                           false
% 2.82/0.99  --trig_cnt_out                          false
% 2.82/0.99  --trig_cnt_out_tolerance                1.
% 2.82/0.99  --trig_cnt_out_sk_spl                   false
% 2.82/0.99  --abstr_cl_out                          false
% 2.82/0.99  
% 2.82/0.99  ------ Global Options
% 2.82/0.99  
% 2.82/0.99  --schedule                              default
% 2.82/0.99  --add_important_lit                     false
% 2.82/0.99  --prop_solver_per_cl                    1000
% 2.82/0.99  --min_unsat_core                        false
% 2.82/0.99  --soft_assumptions                      false
% 2.82/0.99  --soft_lemma_size                       3
% 2.82/0.99  --prop_impl_unit_size                   0
% 2.82/0.99  --prop_impl_unit                        []
% 2.82/0.99  --share_sel_clauses                     true
% 2.82/0.99  --reset_solvers                         false
% 2.82/1.00  --bc_imp_inh                            [conj_cone]
% 2.82/1.00  --conj_cone_tolerance                   3.
% 2.82/1.00  --extra_neg_conj                        none
% 2.82/1.00  --large_theory_mode                     true
% 2.82/1.00  --prolific_symb_bound                   200
% 2.82/1.00  --lt_threshold                          2000
% 2.82/1.00  --clause_weak_htbl                      true
% 2.82/1.00  --gc_record_bc_elim                     false
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing Options
% 2.82/1.00  
% 2.82/1.00  --preprocessing_flag                    true
% 2.82/1.00  --time_out_prep_mult                    0.1
% 2.82/1.00  --splitting_mode                        input
% 2.82/1.00  --splitting_grd                         true
% 2.82/1.00  --splitting_cvd                         false
% 2.82/1.00  --splitting_cvd_svl                     false
% 2.82/1.00  --splitting_nvd                         32
% 2.82/1.00  --sub_typing                            true
% 2.82/1.00  --prep_gs_sim                           true
% 2.82/1.00  --prep_unflatten                        true
% 2.82/1.00  --prep_res_sim                          true
% 2.82/1.00  --prep_upred                            true
% 2.82/1.00  --prep_sem_filter                       exhaustive
% 2.82/1.00  --prep_sem_filter_out                   false
% 2.82/1.00  --pred_elim                             true
% 2.82/1.00  --res_sim_input                         true
% 2.82/1.00  --eq_ax_congr_red                       true
% 2.82/1.00  --pure_diseq_elim                       true
% 2.82/1.00  --brand_transform                       false
% 2.82/1.00  --non_eq_to_eq                          false
% 2.82/1.00  --prep_def_merge                        true
% 2.82/1.00  --prep_def_merge_prop_impl              false
% 2.82/1.00  --prep_def_merge_mbd                    true
% 2.82/1.00  --prep_def_merge_tr_red                 false
% 2.82/1.00  --prep_def_merge_tr_cl                  false
% 2.82/1.00  --smt_preprocessing                     true
% 2.82/1.00  --smt_ac_axioms                         fast
% 2.82/1.00  --preprocessed_out                      false
% 2.82/1.00  --preprocessed_stats                    false
% 2.82/1.00  
% 2.82/1.00  ------ Abstraction refinement Options
% 2.82/1.00  
% 2.82/1.00  --abstr_ref                             []
% 2.82/1.00  --abstr_ref_prep                        false
% 2.82/1.00  --abstr_ref_until_sat                   false
% 2.82/1.00  --abstr_ref_sig_restrict                funpre
% 2.82/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/1.00  --abstr_ref_under                       []
% 2.82/1.00  
% 2.82/1.00  ------ SAT Options
% 2.82/1.00  
% 2.82/1.00  --sat_mode                              false
% 2.82/1.00  --sat_fm_restart_options                ""
% 2.82/1.00  --sat_gr_def                            false
% 2.82/1.00  --sat_epr_types                         true
% 2.82/1.00  --sat_non_cyclic_types                  false
% 2.82/1.00  --sat_finite_models                     false
% 2.82/1.00  --sat_fm_lemmas                         false
% 2.82/1.00  --sat_fm_prep                           false
% 2.82/1.00  --sat_fm_uc_incr                        true
% 2.82/1.00  --sat_out_model                         small
% 2.82/1.00  --sat_out_clauses                       false
% 2.82/1.00  
% 2.82/1.00  ------ QBF Options
% 2.82/1.00  
% 2.82/1.00  --qbf_mode                              false
% 2.82/1.00  --qbf_elim_univ                         false
% 2.82/1.00  --qbf_dom_inst                          none
% 2.82/1.00  --qbf_dom_pre_inst                      false
% 2.82/1.00  --qbf_sk_in                             false
% 2.82/1.00  --qbf_pred_elim                         true
% 2.82/1.00  --qbf_split                             512
% 2.82/1.00  
% 2.82/1.00  ------ BMC1 Options
% 2.82/1.00  
% 2.82/1.00  --bmc1_incremental                      false
% 2.82/1.00  --bmc1_axioms                           reachable_all
% 2.82/1.00  --bmc1_min_bound                        0
% 2.82/1.00  --bmc1_max_bound                        -1
% 2.82/1.00  --bmc1_max_bound_default                -1
% 2.82/1.00  --bmc1_symbol_reachability              true
% 2.82/1.00  --bmc1_property_lemmas                  false
% 2.82/1.00  --bmc1_k_induction                      false
% 2.82/1.00  --bmc1_non_equiv_states                 false
% 2.82/1.00  --bmc1_deadlock                         false
% 2.82/1.00  --bmc1_ucm                              false
% 2.82/1.00  --bmc1_add_unsat_core                   none
% 2.82/1.00  --bmc1_unsat_core_children              false
% 2.82/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/1.00  --bmc1_out_stat                         full
% 2.82/1.00  --bmc1_ground_init                      false
% 2.82/1.00  --bmc1_pre_inst_next_state              false
% 2.82/1.00  --bmc1_pre_inst_state                   false
% 2.82/1.00  --bmc1_pre_inst_reach_state             false
% 2.82/1.00  --bmc1_out_unsat_core                   false
% 2.82/1.00  --bmc1_aig_witness_out                  false
% 2.82/1.00  --bmc1_verbose                          false
% 2.82/1.00  --bmc1_dump_clauses_tptp                false
% 2.82/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.82/1.00  --bmc1_dump_file                        -
% 2.82/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.82/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.82/1.00  --bmc1_ucm_extend_mode                  1
% 2.82/1.00  --bmc1_ucm_init_mode                    2
% 2.82/1.00  --bmc1_ucm_cone_mode                    none
% 2.82/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.82/1.00  --bmc1_ucm_relax_model                  4
% 2.82/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.82/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/1.00  --bmc1_ucm_layered_model                none
% 2.82/1.00  --bmc1_ucm_max_lemma_size               10
% 2.82/1.00  
% 2.82/1.00  ------ AIG Options
% 2.82/1.00  
% 2.82/1.00  --aig_mode                              false
% 2.82/1.00  
% 2.82/1.00  ------ Instantiation Options
% 2.82/1.00  
% 2.82/1.00  --instantiation_flag                    true
% 2.82/1.00  --inst_sos_flag                         false
% 2.82/1.00  --inst_sos_phase                        true
% 2.82/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/1.00  --inst_lit_sel_side                     none
% 2.82/1.00  --inst_solver_per_active                1400
% 2.82/1.00  --inst_solver_calls_frac                1.
% 2.82/1.00  --inst_passive_queue_type               priority_queues
% 2.82/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.82/1.00  --inst_passive_queues_freq              [25;2]
% 2.82/1.00  --inst_dismatching                      true
% 2.82/1.00  --inst_eager_unprocessed_to_passive     true
% 2.82/1.00  --inst_prop_sim_given                   true
% 2.82/1.00  --inst_prop_sim_new                     false
% 2.82/1.00  --inst_subs_new                         false
% 2.82/1.00  --inst_eq_res_simp                      false
% 2.82/1.00  --inst_subs_given                       false
% 2.82/1.00  --inst_orphan_elimination               true
% 2.82/1.00  --inst_learning_loop_flag               true
% 2.82/1.00  --inst_learning_start                   3000
% 2.82/1.00  --inst_learning_factor                  2
% 2.82/1.00  --inst_start_prop_sim_after_learn       3
% 2.82/1.00  --inst_sel_renew                        solver
% 2.82/1.00  --inst_lit_activity_flag                true
% 2.82/1.00  --inst_restr_to_given                   false
% 2.82/1.00  --inst_activity_threshold               500
% 2.82/1.00  --inst_out_proof                        true
% 2.82/1.00  
% 2.82/1.00  ------ Resolution Options
% 2.82/1.00  
% 2.82/1.00  --resolution_flag                       false
% 2.82/1.00  --res_lit_sel                           adaptive
% 2.82/1.00  --res_lit_sel_side                      none
% 2.82/1.00  --res_ordering                          kbo
% 2.82/1.00  --res_to_prop_solver                    active
% 2.82/1.00  --res_prop_simpl_new                    false
% 2.82/1.00  --res_prop_simpl_given                  true
% 2.82/1.00  --res_passive_queue_type                priority_queues
% 2.82/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.82/1.00  --res_passive_queues_freq               [15;5]
% 2.82/1.00  --res_forward_subs                      full
% 2.82/1.00  --res_backward_subs                     full
% 2.82/1.00  --res_forward_subs_resolution           true
% 2.82/1.00  --res_backward_subs_resolution          true
% 2.82/1.00  --res_orphan_elimination                true
% 2.82/1.00  --res_time_limit                        2.
% 2.82/1.00  --res_out_proof                         true
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Options
% 2.82/1.00  
% 2.82/1.00  --superposition_flag                    true
% 2.82/1.00  --sup_passive_queue_type                priority_queues
% 2.82/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.82/1.00  --demod_completeness_check              fast
% 2.82/1.00  --demod_use_ground                      true
% 2.82/1.00  --sup_to_prop_solver                    passive
% 2.82/1.00  --sup_prop_simpl_new                    true
% 2.82/1.00  --sup_prop_simpl_given                  true
% 2.82/1.00  --sup_fun_splitting                     false
% 2.82/1.00  --sup_smt_interval                      50000
% 2.82/1.00  
% 2.82/1.00  ------ Superposition Simplification Setup
% 2.82/1.00  
% 2.82/1.00  --sup_indices_passive                   []
% 2.82/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_full_bw                           [BwDemod]
% 2.82/1.00  --sup_immed_triv                        [TrivRules]
% 2.82/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_immed_bw_main                     []
% 2.82/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.00  
% 2.82/1.00  ------ Combination Options
% 2.82/1.00  
% 2.82/1.00  --comb_res_mult                         3
% 2.82/1.00  --comb_sup_mult                         2
% 2.82/1.00  --comb_inst_mult                        10
% 2.82/1.00  
% 2.82/1.00  ------ Debug Options
% 2.82/1.00  
% 2.82/1.00  --dbg_backtrace                         false
% 2.82/1.00  --dbg_dump_prop_clauses                 false
% 2.82/1.00  --dbg_dump_prop_clauses_file            -
% 2.82/1.00  --dbg_out_stat                          false
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  ------ Proving...
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  % SZS status Theorem for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  fof(f2,axiom,(
% 2.82/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f23,plain,(
% 2.82/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.82/1.00    inference(ennf_transformation,[],[f2])).
% 2.82/1.00  
% 2.82/1.00  fof(f43,plain,(
% 2.82/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.82/1.00    inference(nnf_transformation,[],[f23])).
% 2.82/1.00  
% 2.82/1.00  fof(f44,plain,(
% 2.82/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.82/1.00    inference(rectify,[],[f43])).
% 2.82/1.00  
% 2.82/1.00  fof(f45,plain,(
% 2.82/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f46,plain,(
% 2.82/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 2.82/1.00  
% 2.82/1.00  fof(f62,plain,(
% 2.82/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f46])).
% 2.82/1.00  
% 2.82/1.00  fof(f61,plain,(
% 2.82/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f46])).
% 2.82/1.00  
% 2.82/1.00  fof(f11,axiom,(
% 2.82/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f29,plain,(
% 2.82/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.82/1.00    inference(ennf_transformation,[],[f11])).
% 2.82/1.00  
% 2.82/1.00  fof(f50,plain,(
% 2.82/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.82/1.00    inference(nnf_transformation,[],[f29])).
% 2.82/1.00  
% 2.82/1.00  fof(f74,plain,(
% 2.82/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f50])).
% 2.82/1.00  
% 2.82/1.00  fof(f13,axiom,(
% 2.82/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f51,plain,(
% 2.82/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.82/1.00    inference(nnf_transformation,[],[f13])).
% 2.82/1.00  
% 2.82/1.00  fof(f80,plain,(
% 2.82/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f51])).
% 2.82/1.00  
% 2.82/1.00  fof(f12,axiom,(
% 2.82/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f78,plain,(
% 2.82/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f12])).
% 2.82/1.00  
% 2.82/1.00  fof(f75,plain,(
% 2.82/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f50])).
% 2.82/1.00  
% 2.82/1.00  fof(f1,axiom,(
% 2.82/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f39,plain,(
% 2.82/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.82/1.00    inference(nnf_transformation,[],[f1])).
% 2.82/1.00  
% 2.82/1.00  fof(f40,plain,(
% 2.82/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.82/1.00    inference(rectify,[],[f39])).
% 2.82/1.00  
% 2.82/1.00  fof(f41,plain,(
% 2.82/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f42,plain,(
% 2.82/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 2.82/1.00  
% 2.82/1.00  fof(f58,plain,(
% 2.82/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f42])).
% 2.82/1.00  
% 2.82/1.00  fof(f19,conjecture,(
% 2.82/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f20,negated_conjecture,(
% 2.82/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 2.82/1.00    inference(negated_conjecture,[],[f19])).
% 2.82/1.00  
% 2.82/1.00  fof(f22,plain,(
% 2.82/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 2.82/1.00    inference(pure_predicate_removal,[],[f20])).
% 2.82/1.00  
% 2.82/1.00  fof(f37,plain,(
% 2.82/1.00    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.82/1.00    inference(ennf_transformation,[],[f22])).
% 2.82/1.00  
% 2.82/1.00  fof(f38,plain,(
% 2.82/1.00    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.82/1.00    inference(flattening,[],[f37])).
% 2.82/1.00  
% 2.82/1.00  fof(f56,plain,(
% 2.82/1.00    ( ! [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~m2_connsp_2(k2_struct_0(X0),X0,sK5) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f55,plain,(
% 2.82/1.00    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK4),sK4,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.82/1.00    introduced(choice_axiom,[])).
% 2.82/1.00  
% 2.82/1.00  fof(f57,plain,(
% 2.82/1.00    (~m2_connsp_2(k2_struct_0(sK4),sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 2.82/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f38,f56,f55])).
% 2.82/1.00  
% 2.82/1.00  fof(f91,plain,(
% 2.82/1.00    ~m2_connsp_2(k2_struct_0(sK4),sK4,sK5)),
% 2.82/1.00    inference(cnf_transformation,[],[f57])).
% 2.82/1.00  
% 2.82/1.00  fof(f17,axiom,(
% 2.82/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f34,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.82/1.00    inference(ennf_transformation,[],[f17])).
% 2.82/1.00  
% 2.82/1.00  fof(f35,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/1.00    inference(flattening,[],[f34])).
% 2.82/1.00  
% 2.82/1.00  fof(f52,plain,(
% 2.82/1.00    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/1.00    inference(nnf_transformation,[],[f35])).
% 2.82/1.00  
% 2.82/1.00  fof(f85,plain,(
% 2.82/1.00    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f52])).
% 2.82/1.00  
% 2.82/1.00  fof(f88,plain,(
% 2.82/1.00    v2_pre_topc(sK4)),
% 2.82/1.00    inference(cnf_transformation,[],[f57])).
% 2.82/1.00  
% 2.82/1.00  fof(f89,plain,(
% 2.82/1.00    l1_pre_topc(sK4)),
% 2.82/1.00    inference(cnf_transformation,[],[f57])).
% 2.82/1.00  
% 2.82/1.00  fof(f90,plain,(
% 2.82/1.00    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.82/1.00    inference(cnf_transformation,[],[f57])).
% 2.82/1.00  
% 2.82/1.00  fof(f16,axiom,(
% 2.82/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f32,plain,(
% 2.82/1.00    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.82/1.00    inference(ennf_transformation,[],[f16])).
% 2.82/1.00  
% 2.82/1.00  fof(f33,plain,(
% 2.82/1.00    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.82/1.00    inference(flattening,[],[f32])).
% 2.82/1.00  
% 2.82/1.00  fof(f83,plain,(
% 2.82/1.00    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f33])).
% 2.82/1.00  
% 2.82/1.00  fof(f15,axiom,(
% 2.82/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f31,plain,(
% 2.82/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.82/1.00    inference(ennf_transformation,[],[f15])).
% 2.82/1.00  
% 2.82/1.00  fof(f82,plain,(
% 2.82/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f31])).
% 2.82/1.00  
% 2.82/1.00  fof(f14,axiom,(
% 2.82/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.82/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/1.00  
% 2.82/1.00  fof(f30,plain,(
% 2.82/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.82/1.00    inference(ennf_transformation,[],[f14])).
% 2.82/1.00  
% 2.82/1.00  fof(f81,plain,(
% 2.82/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.82/1.00    inference(cnf_transformation,[],[f30])).
% 2.82/1.00  
% 2.82/1.00  fof(f79,plain,(
% 2.82/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.82/1.00    inference(cnf_transformation,[],[f51])).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2,plain,
% 2.82/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2393,plain,
% 2.82/1.00      ( r1_tarski(k2_struct_0(sK4),X0)
% 2.82/1.00      | ~ r2_hidden(sK1(k2_struct_0(sK4),X0),X0) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3278,plain,
% 2.82/1.00      ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4))
% 2.82/1.00      | ~ r2_hidden(sK1(k2_struct_0(sK4),k2_struct_0(sK4)),k2_struct_0(sK4)) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_2393]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_3,plain,
% 2.82/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2394,plain,
% 2.82/1.00      ( r1_tarski(k2_struct_0(sK4),X0)
% 2.82/1.00      | r2_hidden(sK1(k2_struct_0(sK4),X0),k2_struct_0(sK4)) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2991,plain,
% 2.82/1.00      ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4))
% 2.82/1.00      | r2_hidden(sK1(k2_struct_0(sK4),k2_struct_0(sK4)),k2_struct_0(sK4)) ),
% 2.82/1.00      inference(instantiation,[status(thm)],[c_2394]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_19,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_21,plain,
% 2.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_279,plain,
% 2.82/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.82/1.00      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_280,plain,
% 2.82/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_279]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_746,plain,
% 2.82/1.00      ( ~ r1_tarski(X0,X1)
% 2.82/1.00      | r2_hidden(X2,X3)
% 2.82/1.00      | v1_xboole_0(X3)
% 2.82/1.00      | X0 != X2
% 2.82/1.00      | k1_zfmisc_1(X1) != X3 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_280]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_747,plain,
% 2.82/1.00      ( ~ r1_tarski(X0,X1)
% 2.82/1.00      | r2_hidden(X0,k1_zfmisc_1(X1))
% 2.82/1.00      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_746]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_20,plain,
% 2.82/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.82/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_757,plain,
% 2.82/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.82/1.00      inference(forward_subsumption_resolution,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_747,c_20]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1063,plain,
% 2.82/1.00      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.82/1.00      inference(prop_impl,[status(thm)],[c_757]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1905,plain,
% 2.82/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.82/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_18,plain,
% 2.82/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1,plain,
% 2.82/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_200,plain,
% 2.82/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_18,c_1]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_201,plain,
% 2.82/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_200]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_30,negated_conjecture,
% 2.82/1.00      ( ~ m2_connsp_2(k2_struct_0(sK4),sK4,sK5) ),
% 2.82/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_26,plain,
% 2.82/1.00      ( m2_connsp_2(X0,X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.82/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.82/1.00      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 2.82/1.00      | ~ v2_pre_topc(X1)
% 2.82/1.00      | ~ l1_pre_topc(X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_33,negated_conjecture,
% 2.82/1.00      ( v2_pre_topc(sK4) ),
% 2.82/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_500,plain,
% 2.82/1.00      ( m2_connsp_2(X0,X1,X2)
% 2.82/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.82/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.82/1.00      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 2.82/1.00      | ~ l1_pre_topc(X1)
% 2.82/1.00      | sK4 != X1 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_501,plain,
% 2.82/1.00      ( m2_connsp_2(X0,sK4,X1)
% 2.82/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ r1_tarski(X1,k1_tops_1(sK4,X0))
% 2.82/1.00      | ~ l1_pre_topc(sK4) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_500]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_32,negated_conjecture,
% 2.82/1.00      ( l1_pre_topc(sK4) ),
% 2.82/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_505,plain,
% 2.82/1.00      ( ~ r1_tarski(X1,k1_tops_1(sK4,X0))
% 2.82/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | m2_connsp_2(X0,sK4,X1) ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_501,c_32]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_506,plain,
% 2.82/1.00      ( m2_connsp_2(X0,sK4,X1)
% 2.82/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ r1_tarski(X1,k1_tops_1(sK4,X0)) ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_505]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_560,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ r1_tarski(X1,k1_tops_1(sK4,X0))
% 2.82/1.00      | k2_struct_0(sK4) != X0
% 2.82/1.00      | sK5 != X1
% 2.82/1.00      | sK4 != sK4 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_506]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_561,plain,
% 2.82/1.00      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4))) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_560]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_31,negated_conjecture,
% 2.82/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.82/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_563,plain,
% 2.82/1.00      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.82/1.00      | ~ r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4))) ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_561,c_31]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_791,plain,
% 2.82/1.00      ( ~ r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4)))
% 2.82/1.00      | ~ r2_hidden(X0,X1)
% 2.82/1.00      | k2_struct_0(sK4) != X0
% 2.82/1.00      | k1_zfmisc_1(u1_struct_0(sK4)) != X1 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_201,c_563]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_792,plain,
% 2.82/1.00      ( ~ r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4)))
% 2.82/1.00      | ~ r2_hidden(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_791]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1902,plain,
% 2.82/1.00      ( r1_tarski(sK5,k1_tops_1(sK4,k2_struct_0(sK4))) != iProver_top
% 2.82/1.00      | r2_hidden(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_25,plain,
% 2.82/1.00      ( ~ v2_pre_topc(X0)
% 2.82/1.00      | ~ l1_pre_topc(X0)
% 2.82/1.00      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_468,plain,
% 2.82/1.00      ( ~ l1_pre_topc(X0)
% 2.82/1.00      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 2.82/1.00      | sK4 != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_469,plain,
% 2.82/1.00      ( ~ l1_pre_topc(sK4)
% 2.82/1.00      | k1_tops_1(sK4,k2_struct_0(sK4)) = k2_struct_0(sK4) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_468]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_471,plain,
% 2.82/1.00      ( k1_tops_1(sK4,k2_struct_0(sK4)) = k2_struct_0(sK4) ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_469,c_32]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_24,plain,
% 2.82/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_23,plain,
% 2.82/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.82/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_454,plain,
% 2.82/1.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.82/1.00      inference(resolution,[status(thm)],[c_24,c_23]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_535,plain,
% 2.82/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_454,c_32]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_536,plain,
% 2.82/1.00      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_535]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2012,plain,
% 2.82/1.00      ( r1_tarski(sK5,k2_struct_0(sK4)) != iProver_top
% 2.82/1.00      | r2_hidden(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 2.82/1.00      inference(light_normalisation,[status(thm)],[c_1902,c_471,c_536]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_22,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.82/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_277,plain,
% 2.82/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.82/1.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_278,plain,
% 2.82/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.82/1.00      inference(renaming,[status(thm)],[c_277]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_804,plain,
% 2.82/1.00      ( r1_tarski(X0,X1)
% 2.82/1.00      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X1)
% 2.82/1.00      | sK5 != X0 ),
% 2.82/1.00      inference(resolution_lifted,[status(thm)],[c_278,c_31]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_805,plain,
% 2.82/1.00      ( r1_tarski(sK5,X0)
% 2.82/1.00      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X0) ),
% 2.82/1.00      inference(unflattening,[status(thm)],[c_804]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1901,plain,
% 2.82/1.00      ( k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(X0)
% 2.82/1.00      | r1_tarski(sK5,X0) = iProver_top ),
% 2.82/1.00      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_1956,plain,
% 2.82/1.00      ( k1_zfmisc_1(k2_struct_0(sK4)) != k1_zfmisc_1(X0)
% 2.82/1.00      | r1_tarski(sK5,X0) = iProver_top ),
% 2.82/1.00      inference(light_normalisation,[status(thm)],[c_1901,c_536]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2162,plain,
% 2.82/1.00      ( r1_tarski(sK5,k2_struct_0(sK4)) = iProver_top ),
% 2.82/1.00      inference(equality_resolution,[status(thm)],[c_1956]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2432,plain,
% 2.82/1.00      ( r2_hidden(k2_struct_0(sK4),k1_zfmisc_1(k2_struct_0(sK4))) != iProver_top ),
% 2.82/1.00      inference(global_propositional_subsumption,
% 2.82/1.00                [status(thm)],
% 2.82/1.00                [c_2012,c_2162]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2437,plain,
% 2.82/1.00      ( r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) != iProver_top ),
% 2.82/1.00      inference(superposition,[status(thm)],[c_1905,c_2432]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(c_2438,plain,
% 2.82/1.00      ( ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK4)) ),
% 2.82/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2437]) ).
% 2.82/1.00  
% 2.82/1.00  cnf(contradiction,plain,
% 2.82/1.00      ( $false ),
% 2.82/1.00      inference(minisat,[status(thm)],[c_3278,c_2991,c_2438]) ).
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/1.00  
% 2.82/1.00  ------                               Statistics
% 2.82/1.00  
% 2.82/1.00  ------ General
% 2.82/1.00  
% 2.82/1.00  abstr_ref_over_cycles:                  0
% 2.82/1.00  abstr_ref_under_cycles:                 0
% 2.82/1.00  gc_basic_clause_elim:                   0
% 2.82/1.00  forced_gc_time:                         0
% 2.82/1.00  parsing_time:                           0.014
% 2.82/1.00  unif_index_cands_time:                  0.
% 2.82/1.00  unif_index_add_time:                    0.
% 2.82/1.00  orderings_time:                         0.
% 2.82/1.00  out_proof_time:                         0.013
% 2.82/1.00  total_time:                             0.152
% 2.82/1.00  num_of_symbols:                         54
% 2.82/1.00  num_of_terms:                           2396
% 2.82/1.00  
% 2.82/1.00  ------ Preprocessing
% 2.82/1.00  
% 2.82/1.00  num_of_splits:                          0
% 2.82/1.00  num_of_split_atoms:                     0
% 2.82/1.00  num_of_reused_defs:                     0
% 2.82/1.00  num_eq_ax_congr_red:                    31
% 2.82/1.00  num_of_sem_filtered_clauses:            1
% 2.82/1.00  num_of_subtypes:                        0
% 2.82/1.00  monotx_restored_types:                  0
% 2.82/1.00  sat_num_of_epr_types:                   0
% 2.82/1.00  sat_num_of_non_cyclic_types:            0
% 2.82/1.00  sat_guarded_non_collapsed_types:        0
% 2.82/1.00  num_pure_diseq_elim:                    0
% 2.82/1.00  simp_replaced_by:                       0
% 2.82/1.00  res_preprocessed:                       151
% 2.82/1.00  prep_upred:                             0
% 2.82/1.00  prep_unflattend:                        49
% 2.82/1.00  smt_new_axioms:                         0
% 2.82/1.00  pred_elim_cands:                        4
% 2.82/1.00  pred_elim:                              5
% 2.82/1.00  pred_elim_cl:                           4
% 2.82/1.00  pred_elim_cycles:                       8
% 2.82/1.00  merged_defs:                            16
% 2.82/1.00  merged_defs_ncl:                        0
% 2.82/1.00  bin_hyper_res:                          16
% 2.82/1.00  prep_cycles:                            4
% 2.82/1.00  pred_elim_time:                         0.022
% 2.82/1.00  splitting_time:                         0.
% 2.82/1.00  sem_filter_time:                        0.
% 2.82/1.00  monotx_time:                            0.
% 2.82/1.00  subtype_inf_time:                       0.
% 2.82/1.00  
% 2.82/1.00  ------ Problem properties
% 2.82/1.00  
% 2.82/1.00  clauses:                                30
% 2.82/1.00  conjectures:                            0
% 2.82/1.00  epr:                                    5
% 2.82/1.00  horn:                                   26
% 2.82/1.00  ground:                                 8
% 2.82/1.00  unary:                                  9
% 2.82/1.00  binary:                                 17
% 2.82/1.00  lits:                                   56
% 2.82/1.00  lits_eq:                                14
% 2.82/1.00  fd_pure:                                0
% 2.82/1.00  fd_pseudo:                              0
% 2.82/1.00  fd_cond:                                1
% 2.82/1.00  fd_pseudo_cond:                         1
% 2.82/1.00  ac_symbols:                             0
% 2.82/1.00  
% 2.82/1.00  ------ Propositional Solver
% 2.82/1.00  
% 2.82/1.00  prop_solver_calls:                      26
% 2.82/1.00  prop_fast_solver_calls:                 784
% 2.82/1.00  smt_solver_calls:                       0
% 2.82/1.00  smt_fast_solver_calls:                  0
% 2.82/1.00  prop_num_of_clauses:                    927
% 2.82/1.00  prop_preprocess_simplified:             4947
% 2.82/1.00  prop_fo_subsumed:                       9
% 2.82/1.00  prop_solver_time:                       0.
% 2.82/1.00  smt_solver_time:                        0.
% 2.82/1.00  smt_fast_solver_time:                   0.
% 2.82/1.00  prop_fast_solver_time:                  0.
% 2.82/1.00  prop_unsat_core_time:                   0.
% 2.82/1.00  
% 2.82/1.00  ------ QBF
% 2.82/1.00  
% 2.82/1.00  qbf_q_res:                              0
% 2.82/1.00  qbf_num_tautologies:                    0
% 2.82/1.00  qbf_prep_cycles:                        0
% 2.82/1.00  
% 2.82/1.00  ------ BMC1
% 2.82/1.00  
% 2.82/1.00  bmc1_current_bound:                     -1
% 2.82/1.00  bmc1_last_solved_bound:                 -1
% 2.82/1.00  bmc1_unsat_core_size:                   -1
% 2.82/1.00  bmc1_unsat_core_parents_size:           -1
% 2.82/1.00  bmc1_merge_next_fun:                    0
% 2.82/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.82/1.00  
% 2.82/1.00  ------ Instantiation
% 2.82/1.00  
% 2.82/1.00  inst_num_of_clauses:                    266
% 2.82/1.00  inst_num_in_passive:                    57
% 2.82/1.00  inst_num_in_active:                     134
% 2.82/1.00  inst_num_in_unprocessed:                75
% 2.82/1.00  inst_num_of_loops:                      166
% 2.82/1.00  inst_num_of_learning_restarts:          0
% 2.82/1.00  inst_num_moves_active_passive:          29
% 2.82/1.00  inst_lit_activity:                      0
% 2.82/1.00  inst_lit_activity_moves:                0
% 2.82/1.00  inst_num_tautologies:                   0
% 2.82/1.00  inst_num_prop_implied:                  0
% 2.82/1.00  inst_num_existing_simplified:           0
% 2.82/1.00  inst_num_eq_res_simplified:             0
% 2.82/1.00  inst_num_child_elim:                    0
% 2.82/1.00  inst_num_of_dismatching_blockings:      72
% 2.82/1.00  inst_num_of_non_proper_insts:           225
% 2.82/1.00  inst_num_of_duplicates:                 0
% 2.82/1.00  inst_inst_num_from_inst_to_res:         0
% 2.82/1.00  inst_dismatching_checking_time:         0.
% 2.82/1.00  
% 2.82/1.00  ------ Resolution
% 2.82/1.00  
% 2.82/1.00  res_num_of_clauses:                     0
% 2.82/1.00  res_num_in_passive:                     0
% 2.82/1.00  res_num_in_active:                      0
% 2.82/1.00  res_num_of_loops:                       155
% 2.82/1.00  res_forward_subset_subsumed:            27
% 2.82/1.00  res_backward_subset_subsumed:           4
% 2.82/1.00  res_forward_subsumed:                   4
% 2.82/1.00  res_backward_subsumed:                  0
% 2.82/1.00  res_forward_subsumption_resolution:     3
% 2.82/1.00  res_backward_subsumption_resolution:    0
% 2.82/1.00  res_clause_to_clause_subsumption:       97
% 2.82/1.00  res_orphan_elimination:                 0
% 2.82/1.00  res_tautology_del:                      58
% 2.82/1.00  res_num_eq_res_simplified:              2
% 2.82/1.00  res_num_sel_changes:                    0
% 2.82/1.00  res_moves_from_active_to_pass:          0
% 2.82/1.00  
% 2.82/1.00  ------ Superposition
% 2.82/1.00  
% 2.82/1.00  sup_time_total:                         0.
% 2.82/1.00  sup_time_generating:                    0.
% 2.82/1.00  sup_time_sim_full:                      0.
% 2.82/1.00  sup_time_sim_immed:                     0.
% 2.82/1.00  
% 2.82/1.00  sup_num_of_clauses:                     40
% 2.82/1.00  sup_num_in_active:                      27
% 2.82/1.00  sup_num_in_passive:                     13
% 2.82/1.00  sup_num_of_loops:                       32
% 2.82/1.00  sup_fw_superposition:                   10
% 2.82/1.00  sup_bw_superposition:                   6
% 2.82/1.00  sup_immediate_simplified:               2
% 2.82/1.00  sup_given_eliminated:                   0
% 2.82/1.00  comparisons_done:                       0
% 2.82/1.00  comparisons_avoided:                    0
% 2.82/1.00  
% 2.82/1.00  ------ Simplifications
% 2.82/1.00  
% 2.82/1.00  
% 2.82/1.00  sim_fw_subset_subsumed:                 0
% 2.82/1.00  sim_bw_subset_subsumed:                 0
% 2.82/1.00  sim_fw_subsumed:                        2
% 2.82/1.00  sim_bw_subsumed:                        0
% 2.82/1.00  sim_fw_subsumption_res:                 0
% 2.82/1.00  sim_bw_subsumption_res:                 0
% 2.82/1.00  sim_tautology_del:                      2
% 2.82/1.00  sim_eq_tautology_del:                   1
% 2.82/1.00  sim_eq_res_simp:                        0
% 2.82/1.00  sim_fw_demodulated:                     0
% 2.82/1.00  sim_bw_demodulated:                     5
% 2.82/1.00  sim_light_normalised:                   8
% 2.82/1.00  sim_joinable_taut:                      0
% 2.82/1.00  sim_joinable_simp:                      0
% 2.82/1.00  sim_ac_normalised:                      0
% 2.82/1.00  sim_smt_subsumption:                    0
% 2.82/1.00  
%------------------------------------------------------------------------------

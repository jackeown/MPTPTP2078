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
% DateTime   : Thu Dec  3 12:25:49 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 309 expanded)
%              Number of clauses        :   78 ( 129 expanded)
%              Number of leaves         :   11 (  74 expanded)
%              Depth                    :   21
%              Number of atoms          :  298 (1278 expanded)
%              Number of equality atoms :  105 ( 133 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & ( v2_tex_2(X2,X0)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & ( v2_tex_2(sK2,X0)
          | v2_tex_2(X1,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & ( v2_tex_2(X2,X0)
              | v2_tex_2(sK1,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21,f20,f19])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_309,plain,
    ( r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_627,plain,
    ( r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_310,plain,
    ( k3_xboole_0(X0_39,X1_39) = k3_xboole_0(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_302,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_634,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_307,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | ~ r1_tarski(X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_629,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) = iProver_top
    | r1_tarski(X0_39,X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_168,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_169,plain,
    ( ~ v2_tex_2(X0,sK0)
    | v2_tex_2(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_299,plain,
    ( ~ v2_tex_2(X0_39,sK0)
    | v2_tex_2(X1_39,sK0)
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_169])).

cnf(c_637,plain,
    ( v2_tex_2(X0_39,sK0) != iProver_top
    | v2_tex_2(X1_39,sK0) = iProver_top
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_39,X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_1012,plain,
    ( v2_tex_2(X0_39,sK0) != iProver_top
    | v2_tex_2(X1_39,sK0) = iProver_top
    | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_637])).

cnf(c_1585,plain,
    ( v2_tex_2(X0_39,sK0) != iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_1012])).

cnf(c_1867,plain,
    ( v2_tex_2(k3_xboole_0(u1_struct_0(sK0),X0_39),sK0) != iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top
    | r1_tarski(sK1,k3_xboole_0(u1_struct_0(sK0),X0_39)) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_1585])).

cnf(c_2539,plain,
    ( v2_tex_2(k3_xboole_0(X0_39,u1_struct_0(sK0)),sK0) != iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top
    | r1_tarski(sK1,k3_xboole_0(u1_struct_0(sK0),X0_39)) != iProver_top ),
    inference(superposition,[status(thm)],[c_310,c_1867])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | r1_tarski(X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_714,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_91,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_92,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_91])).

cnf(c_115,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_92])).

cnf(c_300,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | k9_subset_1(X1_39,X2_39,X0_39) = k3_xboole_0(X2_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_115])).

cnf(c_766,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_769,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_1168,plain,
    ( r1_tarski(k3_xboole_0(X0_39,X1_39),X1_39) = iProver_top ),
    inference(superposition,[status(thm)],[c_310,c_627])).

cnf(c_9,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_304,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_632,plain,
    ( v2_tex_2(sK2,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_303,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_633,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_857,plain,
    ( v2_tex_2(X0_39,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_39,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_633,c_637])).

cnf(c_1011,plain,
    ( v2_tex_2(X0_39,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0_39,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_857])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_715,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_308,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X2_39,X0_39)
    | r1_tarski(X2_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_765,plain,
    ( r1_tarski(X0_39,u1_struct_0(sK0))
    | ~ r1_tarski(X0_39,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_772,plain,
    ( r1_tarski(X0_39,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0_39,sK2) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_1335,plain,
    ( v2_tex_2(sK2,sK0) != iProver_top
    | v2_tex_2(X0_39,sK0) = iProver_top
    | r1_tarski(X0_39,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1011,c_15,c_715,c_772])).

cnf(c_1336,plain,
    ( v2_tex_2(X0_39,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0_39,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1335])).

cnf(c_1342,plain,
    ( v2_tex_2(X0_39,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top
    | r1_tarski(X0_39,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_1336])).

cnf(c_1563,plain,
    ( v2_tex_2(k3_xboole_0(X0_39,sK2),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1168,c_1342])).

cnf(c_1576,plain,
    ( v2_tex_2(k3_xboole_0(sK1,sK2),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_319,plain,
    ( ~ v2_tex_2(X0_39,X0_40)
    | v2_tex_2(X1_39,X0_40)
    | X1_39 != X0_39 ),
    theory(equality)).

cnf(c_1911,plain,
    ( ~ v2_tex_2(X0_39,sK0)
    | v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_39 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_3143,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_3145,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2)
    | v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
    | v2_tex_2(k3_xboole_0(sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3143])).

cnf(c_3261,plain,
    ( v2_tex_2(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2539,c_10,c_17,c_714,c_769,c_1576,c_3145])).

cnf(c_858,plain,
    ( v2_tex_2(X0_39,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_39,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_637])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_717,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_718,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_781,plain,
    ( r1_tarski(X0_39,u1_struct_0(sK0))
    | ~ r1_tarski(X0_39,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_788,plain,
    ( r1_tarski(X0_39,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0_39,sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_901,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_39,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_902,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_901])).

cnf(c_936,plain,
    ( v2_tex_2(sK1,sK0) != iProver_top
    | v2_tex_2(X0_39,sK0) = iProver_top
    | r1_tarski(X0_39,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_858,c_14,c_718,c_788,c_902])).

cnf(c_937,plain,
    ( v2_tex_2(X0_39,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0_39,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_936])).

cnf(c_3266,plain,
    ( v2_tex_2(X0_39,sK0) = iProver_top
    | r1_tarski(X0_39,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3261,c_937])).

cnf(c_3457,plain,
    ( v2_tex_2(k3_xboole_0(sK1,X0_39),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_3266])).

cnf(c_630,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) != iProver_top
    | r1_tarski(X0_39,X1_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_1210,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_633,c_630])).

cnf(c_636,plain,
    ( k9_subset_1(X0_39,X1_39,X2_39) = k3_xboole_0(X1_39,X2_39)
    | r1_tarski(X2_39,X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_3172,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
    inference(superposition,[status(thm)],[c_1210,c_636])).

cnf(c_305,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_631,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_3370,plain,
    ( v2_tex_2(k3_xboole_0(sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3172,c_631])).

cnf(c_3627,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3457,c_3370])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:46:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.78/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.00  
% 1.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.78/1.00  
% 1.78/1.00  ------  iProver source info
% 1.78/1.00  
% 1.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.78/1.00  git: non_committed_changes: false
% 1.78/1.00  git: last_make_outside_of_git: false
% 1.78/1.00  
% 1.78/1.00  ------ 
% 1.78/1.00  
% 1.78/1.00  ------ Input Options
% 1.78/1.00  
% 1.78/1.00  --out_options                           all
% 1.78/1.00  --tptp_safe_out                         true
% 1.78/1.00  --problem_path                          ""
% 1.78/1.00  --include_path                          ""
% 1.78/1.00  --clausifier                            res/vclausify_rel
% 1.78/1.00  --clausifier_options                    --mode clausify
% 1.78/1.00  --stdin                                 false
% 1.78/1.00  --stats_out                             all
% 1.78/1.00  
% 1.78/1.00  ------ General Options
% 1.78/1.00  
% 1.78/1.00  --fof                                   false
% 1.78/1.00  --time_out_real                         305.
% 1.78/1.00  --time_out_virtual                      -1.
% 1.78/1.00  --symbol_type_check                     false
% 1.78/1.00  --clausify_out                          false
% 1.78/1.00  --sig_cnt_out                           false
% 1.78/1.00  --trig_cnt_out                          false
% 1.78/1.00  --trig_cnt_out_tolerance                1.
% 1.78/1.00  --trig_cnt_out_sk_spl                   false
% 1.78/1.00  --abstr_cl_out                          false
% 1.78/1.00  
% 1.78/1.00  ------ Global Options
% 1.78/1.00  
% 1.78/1.00  --schedule                              default
% 1.78/1.00  --add_important_lit                     false
% 1.78/1.00  --prop_solver_per_cl                    1000
% 1.78/1.00  --min_unsat_core                        false
% 1.78/1.00  --soft_assumptions                      false
% 1.78/1.00  --soft_lemma_size                       3
% 1.78/1.00  --prop_impl_unit_size                   0
% 1.78/1.00  --prop_impl_unit                        []
% 1.78/1.00  --share_sel_clauses                     true
% 1.78/1.00  --reset_solvers                         false
% 1.78/1.00  --bc_imp_inh                            [conj_cone]
% 1.78/1.00  --conj_cone_tolerance                   3.
% 1.78/1.00  --extra_neg_conj                        none
% 1.78/1.00  --large_theory_mode                     true
% 1.78/1.00  --prolific_symb_bound                   200
% 1.78/1.00  --lt_threshold                          2000
% 1.78/1.00  --clause_weak_htbl                      true
% 1.78/1.00  --gc_record_bc_elim                     false
% 1.78/1.00  
% 1.78/1.00  ------ Preprocessing Options
% 1.78/1.00  
% 1.78/1.00  --preprocessing_flag                    true
% 1.78/1.00  --time_out_prep_mult                    0.1
% 1.78/1.00  --splitting_mode                        input
% 1.78/1.00  --splitting_grd                         true
% 1.78/1.00  --splitting_cvd                         false
% 1.78/1.00  --splitting_cvd_svl                     false
% 1.78/1.00  --splitting_nvd                         32
% 1.78/1.00  --sub_typing                            true
% 1.78/1.00  --prep_gs_sim                           true
% 1.78/1.00  --prep_unflatten                        true
% 1.78/1.00  --prep_res_sim                          true
% 1.78/1.00  --prep_upred                            true
% 1.78/1.00  --prep_sem_filter                       exhaustive
% 1.78/1.00  --prep_sem_filter_out                   false
% 1.78/1.00  --pred_elim                             true
% 1.78/1.00  --res_sim_input                         true
% 1.78/1.00  --eq_ax_congr_red                       true
% 1.78/1.00  --pure_diseq_elim                       true
% 1.78/1.00  --brand_transform                       false
% 1.78/1.00  --non_eq_to_eq                          false
% 1.78/1.00  --prep_def_merge                        true
% 1.78/1.00  --prep_def_merge_prop_impl              false
% 1.78/1.00  --prep_def_merge_mbd                    true
% 1.78/1.00  --prep_def_merge_tr_red                 false
% 1.78/1.00  --prep_def_merge_tr_cl                  false
% 1.78/1.00  --smt_preprocessing                     true
% 1.78/1.00  --smt_ac_axioms                         fast
% 1.78/1.00  --preprocessed_out                      false
% 1.78/1.00  --preprocessed_stats                    false
% 1.78/1.00  
% 1.78/1.00  ------ Abstraction refinement Options
% 1.78/1.00  
% 1.78/1.00  --abstr_ref                             []
% 1.78/1.00  --abstr_ref_prep                        false
% 1.78/1.00  --abstr_ref_until_sat                   false
% 1.78/1.00  --abstr_ref_sig_restrict                funpre
% 1.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/1.00  --abstr_ref_under                       []
% 1.78/1.00  
% 1.78/1.00  ------ SAT Options
% 1.78/1.00  
% 1.78/1.00  --sat_mode                              false
% 1.78/1.00  --sat_fm_restart_options                ""
% 1.78/1.00  --sat_gr_def                            false
% 1.78/1.00  --sat_epr_types                         true
% 1.78/1.00  --sat_non_cyclic_types                  false
% 1.78/1.00  --sat_finite_models                     false
% 1.78/1.00  --sat_fm_lemmas                         false
% 1.78/1.00  --sat_fm_prep                           false
% 1.78/1.00  --sat_fm_uc_incr                        true
% 1.78/1.00  --sat_out_model                         small
% 1.78/1.00  --sat_out_clauses                       false
% 1.78/1.00  
% 1.78/1.00  ------ QBF Options
% 1.78/1.00  
% 1.78/1.00  --qbf_mode                              false
% 1.78/1.00  --qbf_elim_univ                         false
% 1.78/1.00  --qbf_dom_inst                          none
% 1.78/1.00  --qbf_dom_pre_inst                      false
% 1.78/1.00  --qbf_sk_in                             false
% 1.78/1.00  --qbf_pred_elim                         true
% 1.78/1.00  --qbf_split                             512
% 1.78/1.00  
% 1.78/1.00  ------ BMC1 Options
% 1.78/1.00  
% 1.78/1.00  --bmc1_incremental                      false
% 1.78/1.00  --bmc1_axioms                           reachable_all
% 1.78/1.00  --bmc1_min_bound                        0
% 1.78/1.00  --bmc1_max_bound                        -1
% 1.78/1.00  --bmc1_max_bound_default                -1
% 1.78/1.00  --bmc1_symbol_reachability              true
% 1.78/1.00  --bmc1_property_lemmas                  false
% 1.78/1.00  --bmc1_k_induction                      false
% 1.78/1.00  --bmc1_non_equiv_states                 false
% 1.78/1.00  --bmc1_deadlock                         false
% 1.78/1.00  --bmc1_ucm                              false
% 1.78/1.00  --bmc1_add_unsat_core                   none
% 1.78/1.00  --bmc1_unsat_core_children              false
% 1.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/1.00  --bmc1_out_stat                         full
% 1.78/1.00  --bmc1_ground_init                      false
% 1.78/1.00  --bmc1_pre_inst_next_state              false
% 1.78/1.00  --bmc1_pre_inst_state                   false
% 1.78/1.00  --bmc1_pre_inst_reach_state             false
% 1.78/1.00  --bmc1_out_unsat_core                   false
% 1.78/1.00  --bmc1_aig_witness_out                  false
% 1.78/1.00  --bmc1_verbose                          false
% 1.78/1.00  --bmc1_dump_clauses_tptp                false
% 1.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.78/1.00  --bmc1_dump_file                        -
% 1.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.78/1.00  --bmc1_ucm_extend_mode                  1
% 1.78/1.00  --bmc1_ucm_init_mode                    2
% 1.78/1.00  --bmc1_ucm_cone_mode                    none
% 1.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.78/1.00  --bmc1_ucm_relax_model                  4
% 1.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/1.00  --bmc1_ucm_layered_model                none
% 1.78/1.00  --bmc1_ucm_max_lemma_size               10
% 1.78/1.00  
% 1.78/1.00  ------ AIG Options
% 1.78/1.00  
% 1.78/1.00  --aig_mode                              false
% 1.78/1.00  
% 1.78/1.00  ------ Instantiation Options
% 1.78/1.00  
% 1.78/1.00  --instantiation_flag                    true
% 1.78/1.00  --inst_sos_flag                         false
% 1.78/1.00  --inst_sos_phase                        true
% 1.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/1.00  --inst_lit_sel_side                     num_symb
% 1.78/1.00  --inst_solver_per_active                1400
% 1.78/1.00  --inst_solver_calls_frac                1.
% 1.78/1.00  --inst_passive_queue_type               priority_queues
% 1.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/1.00  --inst_passive_queues_freq              [25;2]
% 1.78/1.00  --inst_dismatching                      true
% 1.78/1.00  --inst_eager_unprocessed_to_passive     true
% 1.78/1.00  --inst_prop_sim_given                   true
% 1.78/1.00  --inst_prop_sim_new                     false
% 1.78/1.00  --inst_subs_new                         false
% 1.78/1.00  --inst_eq_res_simp                      false
% 1.78/1.00  --inst_subs_given                       false
% 1.78/1.00  --inst_orphan_elimination               true
% 1.78/1.00  --inst_learning_loop_flag               true
% 1.78/1.00  --inst_learning_start                   3000
% 1.78/1.00  --inst_learning_factor                  2
% 1.78/1.00  --inst_start_prop_sim_after_learn       3
% 1.78/1.00  --inst_sel_renew                        solver
% 1.78/1.00  --inst_lit_activity_flag                true
% 1.78/1.00  --inst_restr_to_given                   false
% 1.78/1.00  --inst_activity_threshold               500
% 1.78/1.00  --inst_out_proof                        true
% 1.78/1.00  
% 1.78/1.00  ------ Resolution Options
% 1.78/1.00  
% 1.78/1.00  --resolution_flag                       true
% 1.78/1.00  --res_lit_sel                           adaptive
% 1.78/1.00  --res_lit_sel_side                      none
% 1.78/1.00  --res_ordering                          kbo
% 1.78/1.00  --res_to_prop_solver                    active
% 1.78/1.00  --res_prop_simpl_new                    false
% 1.78/1.00  --res_prop_simpl_given                  true
% 1.78/1.00  --res_passive_queue_type                priority_queues
% 1.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/1.00  --res_passive_queues_freq               [15;5]
% 1.78/1.00  --res_forward_subs                      full
% 1.78/1.00  --res_backward_subs                     full
% 1.78/1.00  --res_forward_subs_resolution           true
% 1.78/1.00  --res_backward_subs_resolution          true
% 1.78/1.00  --res_orphan_elimination                true
% 1.78/1.00  --res_time_limit                        2.
% 1.78/1.00  --res_out_proof                         true
% 1.78/1.00  
% 1.78/1.00  ------ Superposition Options
% 1.78/1.00  
% 1.78/1.00  --superposition_flag                    true
% 1.78/1.00  --sup_passive_queue_type                priority_queues
% 1.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.78/1.00  --demod_completeness_check              fast
% 1.78/1.00  --demod_use_ground                      true
% 1.78/1.00  --sup_to_prop_solver                    passive
% 1.78/1.00  --sup_prop_simpl_new                    true
% 1.78/1.00  --sup_prop_simpl_given                  true
% 1.78/1.00  --sup_fun_splitting                     false
% 1.78/1.00  --sup_smt_interval                      50000
% 1.78/1.00  
% 1.78/1.00  ------ Superposition Simplification Setup
% 1.78/1.00  
% 1.78/1.00  --sup_indices_passive                   []
% 1.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.00  --sup_full_bw                           [BwDemod]
% 1.78/1.00  --sup_immed_triv                        [TrivRules]
% 1.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.00  --sup_immed_bw_main                     []
% 1.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.00  
% 1.78/1.00  ------ Combination Options
% 1.78/1.00  
% 1.78/1.00  --comb_res_mult                         3
% 1.78/1.00  --comb_sup_mult                         2
% 1.78/1.00  --comb_inst_mult                        10
% 1.78/1.00  
% 1.78/1.00  ------ Debug Options
% 1.78/1.00  
% 1.78/1.00  --dbg_backtrace                         false
% 1.78/1.00  --dbg_dump_prop_clauses                 false
% 1.78/1.00  --dbg_dump_prop_clauses_file            -
% 1.78/1.00  --dbg_out_stat                          false
% 1.78/1.00  ------ Parsing...
% 1.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.78/1.00  
% 1.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.78/1.00  
% 1.78/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.78/1.00  
% 1.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.78/1.00  ------ Proving...
% 1.78/1.00  ------ Problem Properties 
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  clauses                                 12
% 1.78/1.00  conjectures                             4
% 1.78/1.00  EPR                                     2
% 1.78/1.00  Horn                                    11
% 1.78/1.00  unary                                   5
% 1.78/1.00  binary                                  5
% 1.78/1.00  lits                                    23
% 1.78/1.00  lits eq                                 3
% 1.78/1.00  fd_pure                                 0
% 1.78/1.00  fd_pseudo                               0
% 1.78/1.00  fd_cond                                 0
% 1.78/1.00  fd_pseudo_cond                          0
% 1.78/1.00  AC symbols                              0
% 1.78/1.00  
% 1.78/1.00  ------ Schedule dynamic 5 is on 
% 1.78/1.00  
% 1.78/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  ------ 
% 1.78/1.00  Current options:
% 1.78/1.00  ------ 
% 1.78/1.00  
% 1.78/1.00  ------ Input Options
% 1.78/1.00  
% 1.78/1.00  --out_options                           all
% 1.78/1.00  --tptp_safe_out                         true
% 1.78/1.00  --problem_path                          ""
% 1.78/1.00  --include_path                          ""
% 1.78/1.00  --clausifier                            res/vclausify_rel
% 1.78/1.00  --clausifier_options                    --mode clausify
% 1.78/1.00  --stdin                                 false
% 1.78/1.00  --stats_out                             all
% 1.78/1.00  
% 1.78/1.00  ------ General Options
% 1.78/1.00  
% 1.78/1.00  --fof                                   false
% 1.78/1.00  --time_out_real                         305.
% 1.78/1.00  --time_out_virtual                      -1.
% 1.78/1.00  --symbol_type_check                     false
% 1.78/1.00  --clausify_out                          false
% 1.78/1.00  --sig_cnt_out                           false
% 1.78/1.00  --trig_cnt_out                          false
% 1.78/1.00  --trig_cnt_out_tolerance                1.
% 1.78/1.00  --trig_cnt_out_sk_spl                   false
% 1.78/1.00  --abstr_cl_out                          false
% 1.78/1.00  
% 1.78/1.00  ------ Global Options
% 1.78/1.00  
% 1.78/1.00  --schedule                              default
% 1.78/1.00  --add_important_lit                     false
% 1.78/1.00  --prop_solver_per_cl                    1000
% 1.78/1.00  --min_unsat_core                        false
% 1.78/1.00  --soft_assumptions                      false
% 1.78/1.00  --soft_lemma_size                       3
% 1.78/1.00  --prop_impl_unit_size                   0
% 1.78/1.00  --prop_impl_unit                        []
% 1.78/1.00  --share_sel_clauses                     true
% 1.78/1.00  --reset_solvers                         false
% 1.78/1.00  --bc_imp_inh                            [conj_cone]
% 1.78/1.00  --conj_cone_tolerance                   3.
% 1.78/1.00  --extra_neg_conj                        none
% 1.78/1.00  --large_theory_mode                     true
% 1.78/1.00  --prolific_symb_bound                   200
% 1.78/1.00  --lt_threshold                          2000
% 1.78/1.00  --clause_weak_htbl                      true
% 1.78/1.00  --gc_record_bc_elim                     false
% 1.78/1.00  
% 1.78/1.00  ------ Preprocessing Options
% 1.78/1.00  
% 1.78/1.00  --preprocessing_flag                    true
% 1.78/1.00  --time_out_prep_mult                    0.1
% 1.78/1.00  --splitting_mode                        input
% 1.78/1.00  --splitting_grd                         true
% 1.78/1.00  --splitting_cvd                         false
% 1.78/1.00  --splitting_cvd_svl                     false
% 1.78/1.00  --splitting_nvd                         32
% 1.78/1.00  --sub_typing                            true
% 1.78/1.00  --prep_gs_sim                           true
% 1.78/1.00  --prep_unflatten                        true
% 1.78/1.00  --prep_res_sim                          true
% 1.78/1.00  --prep_upred                            true
% 1.78/1.00  --prep_sem_filter                       exhaustive
% 1.78/1.00  --prep_sem_filter_out                   false
% 1.78/1.00  --pred_elim                             true
% 1.78/1.00  --res_sim_input                         true
% 1.78/1.00  --eq_ax_congr_red                       true
% 1.78/1.00  --pure_diseq_elim                       true
% 1.78/1.00  --brand_transform                       false
% 1.78/1.00  --non_eq_to_eq                          false
% 1.78/1.00  --prep_def_merge                        true
% 1.78/1.00  --prep_def_merge_prop_impl              false
% 1.78/1.00  --prep_def_merge_mbd                    true
% 1.78/1.00  --prep_def_merge_tr_red                 false
% 1.78/1.00  --prep_def_merge_tr_cl                  false
% 1.78/1.00  --smt_preprocessing                     true
% 1.78/1.00  --smt_ac_axioms                         fast
% 1.78/1.00  --preprocessed_out                      false
% 1.78/1.00  --preprocessed_stats                    false
% 1.78/1.00  
% 1.78/1.00  ------ Abstraction refinement Options
% 1.78/1.00  
% 1.78/1.00  --abstr_ref                             []
% 1.78/1.00  --abstr_ref_prep                        false
% 1.78/1.00  --abstr_ref_until_sat                   false
% 1.78/1.00  --abstr_ref_sig_restrict                funpre
% 1.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.78/1.00  --abstr_ref_under                       []
% 1.78/1.00  
% 1.78/1.00  ------ SAT Options
% 1.78/1.00  
% 1.78/1.00  --sat_mode                              false
% 1.78/1.00  --sat_fm_restart_options                ""
% 1.78/1.00  --sat_gr_def                            false
% 1.78/1.00  --sat_epr_types                         true
% 1.78/1.00  --sat_non_cyclic_types                  false
% 1.78/1.00  --sat_finite_models                     false
% 1.78/1.00  --sat_fm_lemmas                         false
% 1.78/1.00  --sat_fm_prep                           false
% 1.78/1.00  --sat_fm_uc_incr                        true
% 1.78/1.00  --sat_out_model                         small
% 1.78/1.00  --sat_out_clauses                       false
% 1.78/1.00  
% 1.78/1.00  ------ QBF Options
% 1.78/1.00  
% 1.78/1.00  --qbf_mode                              false
% 1.78/1.00  --qbf_elim_univ                         false
% 1.78/1.00  --qbf_dom_inst                          none
% 1.78/1.00  --qbf_dom_pre_inst                      false
% 1.78/1.00  --qbf_sk_in                             false
% 1.78/1.00  --qbf_pred_elim                         true
% 1.78/1.00  --qbf_split                             512
% 1.78/1.00  
% 1.78/1.00  ------ BMC1 Options
% 1.78/1.00  
% 1.78/1.00  --bmc1_incremental                      false
% 1.78/1.00  --bmc1_axioms                           reachable_all
% 1.78/1.00  --bmc1_min_bound                        0
% 1.78/1.00  --bmc1_max_bound                        -1
% 1.78/1.00  --bmc1_max_bound_default                -1
% 1.78/1.00  --bmc1_symbol_reachability              true
% 1.78/1.00  --bmc1_property_lemmas                  false
% 1.78/1.00  --bmc1_k_induction                      false
% 1.78/1.00  --bmc1_non_equiv_states                 false
% 1.78/1.00  --bmc1_deadlock                         false
% 1.78/1.00  --bmc1_ucm                              false
% 1.78/1.00  --bmc1_add_unsat_core                   none
% 1.78/1.00  --bmc1_unsat_core_children              false
% 1.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.78/1.00  --bmc1_out_stat                         full
% 1.78/1.00  --bmc1_ground_init                      false
% 1.78/1.00  --bmc1_pre_inst_next_state              false
% 1.78/1.00  --bmc1_pre_inst_state                   false
% 1.78/1.00  --bmc1_pre_inst_reach_state             false
% 1.78/1.00  --bmc1_out_unsat_core                   false
% 1.78/1.00  --bmc1_aig_witness_out                  false
% 1.78/1.00  --bmc1_verbose                          false
% 1.78/1.00  --bmc1_dump_clauses_tptp                false
% 1.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.78/1.00  --bmc1_dump_file                        -
% 1.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.78/1.00  --bmc1_ucm_extend_mode                  1
% 1.78/1.00  --bmc1_ucm_init_mode                    2
% 1.78/1.00  --bmc1_ucm_cone_mode                    none
% 1.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.78/1.00  --bmc1_ucm_relax_model                  4
% 1.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.78/1.00  --bmc1_ucm_layered_model                none
% 1.78/1.00  --bmc1_ucm_max_lemma_size               10
% 1.78/1.00  
% 1.78/1.00  ------ AIG Options
% 1.78/1.00  
% 1.78/1.00  --aig_mode                              false
% 1.78/1.00  
% 1.78/1.00  ------ Instantiation Options
% 1.78/1.00  
% 1.78/1.00  --instantiation_flag                    true
% 1.78/1.00  --inst_sos_flag                         false
% 1.78/1.00  --inst_sos_phase                        true
% 1.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.78/1.00  --inst_lit_sel_side                     none
% 1.78/1.00  --inst_solver_per_active                1400
% 1.78/1.00  --inst_solver_calls_frac                1.
% 1.78/1.00  --inst_passive_queue_type               priority_queues
% 1.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.78/1.00  --inst_passive_queues_freq              [25;2]
% 1.78/1.00  --inst_dismatching                      true
% 1.78/1.00  --inst_eager_unprocessed_to_passive     true
% 1.78/1.00  --inst_prop_sim_given                   true
% 1.78/1.00  --inst_prop_sim_new                     false
% 1.78/1.00  --inst_subs_new                         false
% 1.78/1.00  --inst_eq_res_simp                      false
% 1.78/1.00  --inst_subs_given                       false
% 1.78/1.00  --inst_orphan_elimination               true
% 1.78/1.00  --inst_learning_loop_flag               true
% 1.78/1.00  --inst_learning_start                   3000
% 1.78/1.00  --inst_learning_factor                  2
% 1.78/1.00  --inst_start_prop_sim_after_learn       3
% 1.78/1.00  --inst_sel_renew                        solver
% 1.78/1.00  --inst_lit_activity_flag                true
% 1.78/1.00  --inst_restr_to_given                   false
% 1.78/1.00  --inst_activity_threshold               500
% 1.78/1.00  --inst_out_proof                        true
% 1.78/1.00  
% 1.78/1.00  ------ Resolution Options
% 1.78/1.00  
% 1.78/1.00  --resolution_flag                       false
% 1.78/1.00  --res_lit_sel                           adaptive
% 1.78/1.00  --res_lit_sel_side                      none
% 1.78/1.00  --res_ordering                          kbo
% 1.78/1.00  --res_to_prop_solver                    active
% 1.78/1.00  --res_prop_simpl_new                    false
% 1.78/1.00  --res_prop_simpl_given                  true
% 1.78/1.00  --res_passive_queue_type                priority_queues
% 1.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.78/1.00  --res_passive_queues_freq               [15;5]
% 1.78/1.00  --res_forward_subs                      full
% 1.78/1.00  --res_backward_subs                     full
% 1.78/1.00  --res_forward_subs_resolution           true
% 1.78/1.00  --res_backward_subs_resolution          true
% 1.78/1.00  --res_orphan_elimination                true
% 1.78/1.00  --res_time_limit                        2.
% 1.78/1.00  --res_out_proof                         true
% 1.78/1.00  
% 1.78/1.00  ------ Superposition Options
% 1.78/1.00  
% 1.78/1.00  --superposition_flag                    true
% 1.78/1.00  --sup_passive_queue_type                priority_queues
% 1.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.78/1.00  --demod_completeness_check              fast
% 1.78/1.00  --demod_use_ground                      true
% 1.78/1.00  --sup_to_prop_solver                    passive
% 1.78/1.00  --sup_prop_simpl_new                    true
% 1.78/1.00  --sup_prop_simpl_given                  true
% 1.78/1.00  --sup_fun_splitting                     false
% 1.78/1.00  --sup_smt_interval                      50000
% 1.78/1.00  
% 1.78/1.00  ------ Superposition Simplification Setup
% 1.78/1.00  
% 1.78/1.00  --sup_indices_passive                   []
% 1.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.00  --sup_full_bw                           [BwDemod]
% 1.78/1.00  --sup_immed_triv                        [TrivRules]
% 1.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.00  --sup_immed_bw_main                     []
% 1.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.78/1.00  
% 1.78/1.00  ------ Combination Options
% 1.78/1.00  
% 1.78/1.00  --comb_res_mult                         3
% 1.78/1.00  --comb_sup_mult                         2
% 1.78/1.00  --comb_inst_mult                        10
% 1.78/1.00  
% 1.78/1.00  ------ Debug Options
% 1.78/1.00  
% 1.78/1.00  --dbg_backtrace                         false
% 1.78/1.00  --dbg_dump_prop_clauses                 false
% 1.78/1.00  --dbg_dump_prop_clauses_file            -
% 1.78/1.00  --dbg_out_stat                          false
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  ------ Proving...
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  % SZS status Theorem for theBenchmark.p
% 1.78/1.00  
% 1.78/1.00   Resolution empty clause
% 1.78/1.00  
% 1.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.78/1.00  
% 1.78/1.00  fof(f2,axiom,(
% 1.78/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f24,plain,(
% 1.78/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f2])).
% 1.78/1.00  
% 1.78/1.00  fof(f1,axiom,(
% 1.78/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f23,plain,(
% 1.78/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f1])).
% 1.78/1.00  
% 1.78/1.00  fof(f8,conjecture,(
% 1.78/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f9,negated_conjecture,(
% 1.78/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.78/1.00    inference(negated_conjecture,[],[f8])).
% 1.78/1.00  
% 1.78/1.00  fof(f16,plain,(
% 1.78/1.00    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.78/1.00    inference(ennf_transformation,[],[f9])).
% 1.78/1.00  
% 1.78/1.00  fof(f17,plain,(
% 1.78/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.78/1.00    inference(flattening,[],[f16])).
% 1.78/1.00  
% 1.78/1.00  fof(f21,plain,(
% 1.78/1.00    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & (v2_tex_2(sK2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f20,plain,(
% 1.78/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f19,plain,(
% 1.78/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.78/1.00    introduced(choice_axiom,[])).
% 1.78/1.00  
% 1.78/1.00  fof(f22,plain,(
% 1.78/1.00    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21,f20,f19])).
% 1.78/1.00  
% 1.78/1.00  fof(f32,plain,(
% 1.78/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/1.00    inference(cnf_transformation,[],[f22])).
% 1.78/1.00  
% 1.78/1.00  fof(f6,axiom,(
% 1.78/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f18,plain,(
% 1.78/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.78/1.00    inference(nnf_transformation,[],[f6])).
% 1.78/1.00  
% 1.78/1.00  fof(f29,plain,(
% 1.78/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f18])).
% 1.78/1.00  
% 1.78/1.00  fof(f7,axiom,(
% 1.78/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 1.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f14,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/1.00    inference(ennf_transformation,[],[f7])).
% 1.78/1.00  
% 1.78/1.00  fof(f15,plain,(
% 1.78/1.00    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/1.00    inference(flattening,[],[f14])).
% 1.78/1.00  
% 1.78/1.00  fof(f30,plain,(
% 1.78/1.00    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f15])).
% 1.78/1.00  
% 1.78/1.00  fof(f31,plain,(
% 1.78/1.00    l1_pre_topc(sK0)),
% 1.78/1.00    inference(cnf_transformation,[],[f22])).
% 1.78/1.00  
% 1.78/1.00  fof(f33,plain,(
% 1.78/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/1.00    inference(cnf_transformation,[],[f22])).
% 1.78/1.00  
% 1.78/1.00  fof(f35,plain,(
% 1.78/1.00    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.78/1.00    inference(cnf_transformation,[],[f22])).
% 1.78/1.00  
% 1.78/1.00  fof(f28,plain,(
% 1.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.78/1.00    inference(cnf_transformation,[],[f18])).
% 1.78/1.00  
% 1.78/1.00  fof(f5,axiom,(
% 1.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 1.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f13,plain,(
% 1.78/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.78/1.00    inference(ennf_transformation,[],[f5])).
% 1.78/1.00  
% 1.78/1.00  fof(f27,plain,(
% 1.78/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.78/1.00    inference(cnf_transformation,[],[f13])).
% 1.78/1.00  
% 1.78/1.00  fof(f34,plain,(
% 1.78/1.00    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 1.78/1.00    inference(cnf_transformation,[],[f22])).
% 1.78/1.00  
% 1.78/1.00  fof(f3,axiom,(
% 1.78/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.78/1.00  
% 1.78/1.00  fof(f10,plain,(
% 1.78/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.78/1.00    inference(ennf_transformation,[],[f3])).
% 1.78/1.00  
% 1.78/1.00  fof(f11,plain,(
% 1.78/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.78/1.00    inference(flattening,[],[f10])).
% 1.78/1.00  
% 1.78/1.00  fof(f25,plain,(
% 1.78/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.78/1.00    inference(cnf_transformation,[],[f11])).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1,plain,
% 1.78/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f24]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_309,plain,
% 1.78/1.00      ( r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_627,plain,
% 1.78/1.00      ( r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_0,plain,
% 1.78/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f23]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_310,plain,
% 1.78/1.00      ( k3_xboole_0(X0_39,X1_39) = k3_xboole_0(X1_39,X0_39) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_11,negated_conjecture,
% 1.78/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.78/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_302,negated_conjecture,
% 1.78/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_634,plain,
% 1.78/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_5,plain,
% 1.78/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.78/1.00      inference(cnf_transformation,[],[f29]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_307,plain,
% 1.78/1.00      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) | ~ r1_tarski(X0_39,X1_39) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_629,plain,
% 1.78/1.00      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) = iProver_top
% 1.78/1.00      | r1_tarski(X0_39,X1_39) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_7,plain,
% 1.78/1.00      ( ~ v2_tex_2(X0,X1)
% 1.78/1.00      | v2_tex_2(X2,X1)
% 1.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/1.00      | ~ r1_tarski(X2,X0)
% 1.78/1.00      | ~ l1_pre_topc(X1) ),
% 1.78/1.00      inference(cnf_transformation,[],[f30]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_12,negated_conjecture,
% 1.78/1.00      ( l1_pre_topc(sK0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_168,plain,
% 1.78/1.00      ( ~ v2_tex_2(X0,X1)
% 1.78/1.00      | v2_tex_2(X2,X1)
% 1.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.78/1.00      | ~ r1_tarski(X2,X0)
% 1.78/1.00      | sK0 != X1 ),
% 1.78/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_169,plain,
% 1.78/1.00      ( ~ v2_tex_2(X0,sK0)
% 1.78/1.00      | v2_tex_2(X1,sK0)
% 1.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.78/1.00      | ~ r1_tarski(X1,X0) ),
% 1.78/1.00      inference(unflattening,[status(thm)],[c_168]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_299,plain,
% 1.78/1.00      ( ~ v2_tex_2(X0_39,sK0)
% 1.78/1.00      | v2_tex_2(X1_39,sK0)
% 1.78/1.00      | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.78/1.00      | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.78/1.00      | ~ r1_tarski(X1_39,X0_39) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_169]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_637,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) != iProver_top
% 1.78/1.00      | v2_tex_2(X1_39,sK0) = iProver_top
% 1.78/1.00      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.78/1.00      | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.78/1.00      | r1_tarski(X1_39,X0_39) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1012,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) != iProver_top
% 1.78/1.00      | v2_tex_2(X1_39,sK0) = iProver_top
% 1.78/1.00      | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.78/1.00      | r1_tarski(X1_39,X0_39) != iProver_top
% 1.78/1.00      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_629,c_637]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1585,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) != iProver_top
% 1.78/1.00      | v2_tex_2(sK1,sK0) = iProver_top
% 1.78/1.00      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
% 1.78/1.00      | r1_tarski(sK1,X0_39) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_634,c_1012]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1867,plain,
% 1.78/1.00      ( v2_tex_2(k3_xboole_0(u1_struct_0(sK0),X0_39),sK0) != iProver_top
% 1.78/1.00      | v2_tex_2(sK1,sK0) = iProver_top
% 1.78/1.00      | r1_tarski(sK1,k3_xboole_0(u1_struct_0(sK0),X0_39)) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_627,c_1585]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2539,plain,
% 1.78/1.00      ( v2_tex_2(k3_xboole_0(X0_39,u1_struct_0(sK0)),sK0) != iProver_top
% 1.78/1.00      | v2_tex_2(sK1,sK0) = iProver_top
% 1.78/1.00      | r1_tarski(sK1,k3_xboole_0(u1_struct_0(sK0),X0_39)) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_310,c_1867]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_10,negated_conjecture,
% 1.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.78/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_8,negated_conjecture,
% 1.78/1.00      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_17,plain,
% 1.78/1.00      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_6,plain,
% 1.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.78/1.00      inference(cnf_transformation,[],[f28]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_306,plain,
% 1.78/1.00      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) | r1_tarski(X0_39,X1_39) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_714,plain,
% 1.78/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.78/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_306]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_4,plain,
% 1.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.78/1.00      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f27]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_91,plain,
% 1.78/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.78/1.00      inference(prop_impl,[status(thm)],[c_5]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_92,plain,
% 1.78/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_91]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_115,plain,
% 1.78/1.00      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 1.78/1.00      inference(bin_hyper_res,[status(thm)],[c_4,c_92]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_300,plain,
% 1.78/1.00      ( ~ r1_tarski(X0_39,X1_39)
% 1.78/1.00      | k9_subset_1(X1_39,X2_39,X0_39) = k3_xboole_0(X2_39,X0_39) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_115]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_766,plain,
% 1.78/1.00      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 1.78/1.00      | k9_subset_1(u1_struct_0(sK0),X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_300]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_769,plain,
% 1.78/1.00      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 1.78/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_766]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1168,plain,
% 1.78/1.00      ( r1_tarski(k3_xboole_0(X0_39,X1_39),X1_39) = iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_310,c_627]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_9,negated_conjecture,
% 1.78/1.00      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 1.78/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_304,negated_conjecture,
% 1.78/1.00      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_632,plain,
% 1.78/1.00      ( v2_tex_2(sK2,sK0) = iProver_top | v2_tex_2(sK1,sK0) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_303,negated_conjecture,
% 1.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_633,plain,
% 1.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_857,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) = iProver_top
% 1.78/1.00      | v2_tex_2(sK2,sK0) != iProver_top
% 1.78/1.00      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK2) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_633,c_637]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1011,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) = iProver_top
% 1.78/1.00      | v2_tex_2(sK2,sK0) != iProver_top
% 1.78/1.00      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK2) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_629,c_857]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_15,plain,
% 1.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_715,plain,
% 1.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.78/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_2,plain,
% 1.78/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 1.78/1.00      inference(cnf_transformation,[],[f25]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_308,plain,
% 1.78/1.00      ( ~ r1_tarski(X0_39,X1_39)
% 1.78/1.00      | ~ r1_tarski(X2_39,X0_39)
% 1.78/1.00      | r1_tarski(X2_39,X1_39) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_765,plain,
% 1.78/1.00      ( r1_tarski(X0_39,u1_struct_0(sK0))
% 1.78/1.00      | ~ r1_tarski(X0_39,sK2)
% 1.78/1.00      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_308]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_772,plain,
% 1.78/1.00      ( r1_tarski(X0_39,u1_struct_0(sK0)) = iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK2) != iProver_top
% 1.78/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1335,plain,
% 1.78/1.00      ( v2_tex_2(sK2,sK0) != iProver_top
% 1.78/1.00      | v2_tex_2(X0_39,sK0) = iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK2) != iProver_top ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_1011,c_15,c_715,c_772]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1336,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) = iProver_top
% 1.78/1.00      | v2_tex_2(sK2,sK0) != iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK2) != iProver_top ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_1335]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1342,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) = iProver_top
% 1.78/1.00      | v2_tex_2(sK1,sK0) = iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK2) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_632,c_1336]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1563,plain,
% 1.78/1.00      ( v2_tex_2(k3_xboole_0(X0_39,sK2),sK0) = iProver_top
% 1.78/1.00      | v2_tex_2(sK1,sK0) = iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_1168,c_1342]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1576,plain,
% 1.78/1.00      ( v2_tex_2(k3_xboole_0(sK1,sK2),sK0) = iProver_top
% 1.78/1.00      | v2_tex_2(sK1,sK0) = iProver_top ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_1563]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_319,plain,
% 1.78/1.00      ( ~ v2_tex_2(X0_39,X0_40) | v2_tex_2(X1_39,X0_40) | X1_39 != X0_39 ),
% 1.78/1.00      theory(equality) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1911,plain,
% 1.78/1.00      ( ~ v2_tex_2(X0_39,sK0)
% 1.78/1.00      | v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 1.78/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_39 ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_319]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3143,plain,
% 1.78/1.00      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 1.78/1.00      | ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
% 1.78/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_1911]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3145,plain,
% 1.78/1.00      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2)
% 1.78/1.00      | v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
% 1.78/1.00      | v2_tex_2(k3_xboole_0(sK1,sK2),sK0) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_3143]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3261,plain,
% 1.78/1.00      ( v2_tex_2(sK1,sK0) = iProver_top ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_2539,c_10,c_17,c_714,c_769,c_1576,c_3145]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_858,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) = iProver_top
% 1.78/1.00      | v2_tex_2(sK1,sK0) != iProver_top
% 1.78/1.00      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK1) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_634,c_637]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_14,plain,
% 1.78/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_717,plain,
% 1.78/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.78/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_306]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_718,plain,
% 1.78/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.78/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_781,plain,
% 1.78/1.00      ( r1_tarski(X0_39,u1_struct_0(sK0))
% 1.78/1.00      | ~ r1_tarski(X0_39,sK1)
% 1.78/1.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_308]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_788,plain,
% 1.78/1.00      ( r1_tarski(X0_39,u1_struct_0(sK0)) = iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK1) != iProver_top
% 1.78/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_901,plain,
% 1.78/1.00      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.78/1.00      | ~ r1_tarski(X0_39,u1_struct_0(sK0)) ),
% 1.78/1.00      inference(instantiation,[status(thm)],[c_307]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_902,plain,
% 1.78/1.00      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.78/1.00      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_901]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_936,plain,
% 1.78/1.00      ( v2_tex_2(sK1,sK0) != iProver_top
% 1.78/1.00      | v2_tex_2(X0_39,sK0) = iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK1) != iProver_top ),
% 1.78/1.00      inference(global_propositional_subsumption,
% 1.78/1.00                [status(thm)],
% 1.78/1.00                [c_858,c_14,c_718,c_788,c_902]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_937,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) = iProver_top
% 1.78/1.00      | v2_tex_2(sK1,sK0) != iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK1) != iProver_top ),
% 1.78/1.00      inference(renaming,[status(thm)],[c_936]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3266,plain,
% 1.78/1.00      ( v2_tex_2(X0_39,sK0) = iProver_top
% 1.78/1.00      | r1_tarski(X0_39,sK1) != iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_3261,c_937]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3457,plain,
% 1.78/1.00      ( v2_tex_2(k3_xboole_0(sK1,X0_39),sK0) = iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_627,c_3266]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_630,plain,
% 1.78/1.00      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) != iProver_top
% 1.78/1.00      | r1_tarski(X0_39,X1_39) = iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_1210,plain,
% 1.78/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_633,c_630]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_636,plain,
% 1.78/1.00      ( k9_subset_1(X0_39,X1_39,X2_39) = k3_xboole_0(X1_39,X2_39)
% 1.78/1.00      | r1_tarski(X2_39,X0_39) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3172,plain,
% 1.78/1.00      ( k9_subset_1(u1_struct_0(sK0),X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_1210,c_636]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_305,negated_conjecture,
% 1.78/1.00      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 1.78/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_631,plain,
% 1.78/1.00      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 1.78/1.00      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3370,plain,
% 1.78/1.00      ( v2_tex_2(k3_xboole_0(sK1,sK2),sK0) != iProver_top ),
% 1.78/1.00      inference(demodulation,[status(thm)],[c_3172,c_631]) ).
% 1.78/1.00  
% 1.78/1.00  cnf(c_3627,plain,
% 1.78/1.00      ( $false ),
% 1.78/1.00      inference(superposition,[status(thm)],[c_3457,c_3370]) ).
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.78/1.00  
% 1.78/1.00  ------                               Statistics
% 1.78/1.00  
% 1.78/1.00  ------ General
% 1.78/1.00  
% 1.78/1.00  abstr_ref_over_cycles:                  0
% 1.78/1.00  abstr_ref_under_cycles:                 0
% 1.78/1.00  gc_basic_clause_elim:                   0
% 1.78/1.00  forced_gc_time:                         0
% 1.78/1.00  parsing_time:                           0.014
% 1.78/1.00  unif_index_cands_time:                  0.
% 1.78/1.00  unif_index_add_time:                    0.
% 1.78/1.00  orderings_time:                         0.
% 1.78/1.00  out_proof_time:                         0.009
% 1.78/1.00  total_time:                             0.144
% 1.78/1.00  num_of_symbols:                         45
% 1.78/1.00  num_of_terms:                           4404
% 1.78/1.00  
% 1.78/1.00  ------ Preprocessing
% 1.78/1.00  
% 1.78/1.00  num_of_splits:                          0
% 1.78/1.00  num_of_split_atoms:                     0
% 1.78/1.00  num_of_reused_defs:                     0
% 1.78/1.00  num_eq_ax_congr_red:                    11
% 1.78/1.00  num_of_sem_filtered_clauses:            1
% 1.78/1.00  num_of_subtypes:                        3
% 1.78/1.00  monotx_restored_types:                  0
% 1.78/1.00  sat_num_of_epr_types:                   0
% 1.78/1.00  sat_num_of_non_cyclic_types:            0
% 1.78/1.00  sat_guarded_non_collapsed_types:        0
% 1.78/1.00  num_pure_diseq_elim:                    0
% 1.78/1.00  simp_replaced_by:                       0
% 1.78/1.00  res_preprocessed:                       66
% 1.78/1.00  prep_upred:                             0
% 1.78/1.00  prep_unflattend:                        1
% 1.78/1.00  smt_new_axioms:                         0
% 1.78/1.00  pred_elim_cands:                        3
% 1.78/1.00  pred_elim:                              1
% 1.78/1.00  pred_elim_cl:                           1
% 1.78/1.00  pred_elim_cycles:                       3
% 1.78/1.00  merged_defs:                            8
% 1.78/1.00  merged_defs_ncl:                        0
% 1.78/1.00  bin_hyper_res:                          10
% 1.78/1.00  prep_cycles:                            4
% 1.78/1.00  pred_elim_time:                         0.001
% 1.78/1.00  splitting_time:                         0.
% 1.78/1.00  sem_filter_time:                        0.
% 1.78/1.00  monotx_time:                            0.
% 1.78/1.00  subtype_inf_time:                       0.
% 1.78/1.00  
% 1.78/1.00  ------ Problem properties
% 1.78/1.00  
% 1.78/1.00  clauses:                                12
% 1.78/1.00  conjectures:                            4
% 1.78/1.00  epr:                                    2
% 1.78/1.00  horn:                                   11
% 1.78/1.00  ground:                                 4
% 1.78/1.00  unary:                                  5
% 1.78/1.00  binary:                                 5
% 1.78/1.00  lits:                                   23
% 1.78/1.00  lits_eq:                                3
% 1.78/1.00  fd_pure:                                0
% 1.78/1.00  fd_pseudo:                              0
% 1.78/1.00  fd_cond:                                0
% 1.78/1.00  fd_pseudo_cond:                         0
% 1.78/1.00  ac_symbols:                             0
% 1.78/1.00  
% 1.78/1.00  ------ Propositional Solver
% 1.78/1.00  
% 1.78/1.00  prop_solver_calls:                      28
% 1.78/1.00  prop_fast_solver_calls:                 389
% 1.78/1.00  smt_solver_calls:                       0
% 1.78/1.00  smt_fast_solver_calls:                  0
% 1.78/1.00  prop_num_of_clauses:                    1449
% 1.78/1.00  prop_preprocess_simplified:             4686
% 1.78/1.00  prop_fo_subsumed:                       7
% 1.78/1.00  prop_solver_time:                       0.
% 1.78/1.00  smt_solver_time:                        0.
% 1.78/1.00  smt_fast_solver_time:                   0.
% 1.78/1.00  prop_fast_solver_time:                  0.
% 1.78/1.00  prop_unsat_core_time:                   0.
% 1.78/1.00  
% 1.78/1.00  ------ QBF
% 1.78/1.00  
% 1.78/1.00  qbf_q_res:                              0
% 1.78/1.00  qbf_num_tautologies:                    0
% 1.78/1.00  qbf_prep_cycles:                        0
% 1.78/1.00  
% 1.78/1.00  ------ BMC1
% 1.78/1.00  
% 1.78/1.00  bmc1_current_bound:                     -1
% 1.78/1.00  bmc1_last_solved_bound:                 -1
% 1.78/1.00  bmc1_unsat_core_size:                   -1
% 1.78/1.00  bmc1_unsat_core_parents_size:           -1
% 1.78/1.00  bmc1_merge_next_fun:                    0
% 1.78/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.78/1.00  
% 1.78/1.00  ------ Instantiation
% 1.78/1.00  
% 1.78/1.00  inst_num_of_clauses:                    437
% 1.78/1.00  inst_num_in_passive:                    175
% 1.78/1.00  inst_num_in_active:                     191
% 1.78/1.00  inst_num_in_unprocessed:                71
% 1.78/1.00  inst_num_of_loops:                      220
% 1.78/1.00  inst_num_of_learning_restarts:          0
% 1.78/1.00  inst_num_moves_active_passive:          23
% 1.78/1.00  inst_lit_activity:                      0
% 1.78/1.00  inst_lit_activity_moves:                0
% 1.78/1.00  inst_num_tautologies:                   0
% 1.78/1.00  inst_num_prop_implied:                  0
% 1.78/1.00  inst_num_existing_simplified:           0
% 1.78/1.00  inst_num_eq_res_simplified:             0
% 1.78/1.00  inst_num_child_elim:                    0
% 1.78/1.00  inst_num_of_dismatching_blockings:      244
% 1.78/1.00  inst_num_of_non_proper_insts:           344
% 1.78/1.00  inst_num_of_duplicates:                 0
% 1.78/1.00  inst_inst_num_from_inst_to_res:         0
% 1.78/1.00  inst_dismatching_checking_time:         0.
% 1.78/1.00  
% 1.78/1.00  ------ Resolution
% 1.78/1.00  
% 1.78/1.00  res_num_of_clauses:                     0
% 1.78/1.00  res_num_in_passive:                     0
% 1.78/1.00  res_num_in_active:                      0
% 1.78/1.00  res_num_of_loops:                       70
% 1.78/1.00  res_forward_subset_subsumed:            27
% 1.78/1.00  res_backward_subset_subsumed:           8
% 1.78/1.00  res_forward_subsumed:                   0
% 1.78/1.00  res_backward_subsumed:                  0
% 1.78/1.00  res_forward_subsumption_resolution:     0
% 1.78/1.00  res_backward_subsumption_resolution:    0
% 1.78/1.00  res_clause_to_clause_subsumption:       140
% 1.78/1.00  res_orphan_elimination:                 0
% 1.78/1.00  res_tautology_del:                      40
% 1.78/1.00  res_num_eq_res_simplified:              0
% 1.78/1.00  res_num_sel_changes:                    0
% 1.78/1.00  res_moves_from_active_to_pass:          0
% 1.78/1.00  
% 1.78/1.00  ------ Superposition
% 1.78/1.00  
% 1.78/1.00  sup_time_total:                         0.
% 1.78/1.00  sup_time_generating:                    0.
% 1.78/1.00  sup_time_sim_full:                      0.
% 1.78/1.00  sup_time_sim_immed:                     0.
% 1.78/1.00  
% 1.78/1.00  sup_num_of_clauses:                     48
% 1.78/1.00  sup_num_in_active:                      38
% 1.78/1.00  sup_num_in_passive:                     10
% 1.78/1.00  sup_num_of_loops:                       42
% 1.78/1.00  sup_fw_superposition:                   66
% 1.78/1.00  sup_bw_superposition:                   4
% 1.78/1.00  sup_immediate_simplified:               3
% 1.78/1.00  sup_given_eliminated:                   0
% 1.78/1.00  comparisons_done:                       0
% 1.78/1.00  comparisons_avoided:                    0
% 1.78/1.00  
% 1.78/1.00  ------ Simplifications
% 1.78/1.00  
% 1.78/1.00  
% 1.78/1.00  sim_fw_subset_subsumed:                 2
% 1.78/1.00  sim_bw_subset_subsumed:                 3
% 1.78/1.00  sim_fw_subsumed:                        1
% 1.78/1.00  sim_bw_subsumed:                        0
% 1.78/1.00  sim_fw_subsumption_res:                 0
% 1.78/1.00  sim_bw_subsumption_res:                 0
% 1.78/1.00  sim_tautology_del:                      4
% 1.78/1.00  sim_eq_tautology_del:                   0
% 1.78/1.00  sim_eq_res_simp:                        0
% 1.78/1.00  sim_fw_demodulated:                     0
% 1.78/1.00  sim_bw_demodulated:                     3
% 1.78/1.00  sim_light_normalised:                   0
% 1.78/1.00  sim_joinable_taut:                      0
% 1.78/1.00  sim_joinable_simp:                      0
% 1.78/1.00  sim_ac_normalised:                      0
% 1.78/1.00  sim_smt_subsumption:                    0
% 1.78/1.00  
%------------------------------------------------------------------------------

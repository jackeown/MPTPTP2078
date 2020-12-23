%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:23 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_22)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) != k2_tops_1(X0,sK1)
          | ~ v3_pre_topc(sK1,X0) )
        & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) = k2_tops_1(X0,sK1)
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) != k2_tops_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) = k2_tops_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_206,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_738,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_216,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | m1_subset_1(k2_pre_topc(X0_44,X0_45),k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_724,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_44,X0_45),k1_zfmisc_1(u1_struct_0(X0_44))) = iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_47))
    | k7_subset_1(X0_47,X0_45,X1_45) = k4_xboole_0(X0_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_723,plain,
    ( k7_subset_1(X0_47,X0_45,X1_45) = k4_xboole_0(X0_45,X1_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(X0_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_1515,plain,
    ( k7_subset_1(u1_struct_0(X0_44),k2_pre_topc(X0_44,X0_45),X1_45) = k4_xboole_0(k2_pre_topc(X0_44,X0_45),X1_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_724,c_723])).

cnf(c_10854,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0_45) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0_45)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_1515])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11392,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0_45) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0_45) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10854,c_19])).

cnf(c_14,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_207,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_737,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_211,plain,
    ( ~ v3_pre_topc(X0_45,X0_44)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(X1_44)))
    | ~ v2_pre_topc(X1_44)
    | ~ l1_pre_topc(X1_44)
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,X0_45) = X0_45 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_226,plain,
    ( ~ v3_pre_topc(X0_45,X0_44)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,X0_45) = X0_45
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_211])).

cnf(c_732,plain,
    ( k1_tops_1(X0_44,X0_45) = X0_45
    | v3_pre_topc(X0_45,X0_44) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_227,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_211])).

cnf(c_279,plain,
    ( sP3_iProver_split = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_280,plain,
    ( k1_tops_1(X0_44,X0_45) = X0_45
    | v3_pre_topc(X0_45,X0_44) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_211])).

cnf(c_283,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | v2_pre_topc(X0_44) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_285,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_5321,plain,
    ( l1_pre_topc(X0_44) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | v3_pre_topc(X0_45,X0_44) != iProver_top
    | k1_tops_1(X0_44,X0_45) = X0_45 ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_18,c_19,c_20,c_279,c_280,c_285])).

cnf(c_5322,plain,
    ( k1_tops_1(X0_44,X0_45) = X0_45
    | v3_pre_topc(X0_45,X0_44) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(renaming,[status(thm)],[c_5321])).

cnf(c_5329,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | v3_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_5322])).

cnf(c_13,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_208,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_292,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_229,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_2813,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_230,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1246,plain,
    ( X0_45 != X1_45
    | X1_45 = X0_45 ),
    inference(resolution,[status(thm)],[c_230,c_229])).

cnf(c_2275,plain,
    ( v3_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[status(thm)],[c_1246,c_207])).

cnf(c_2626,plain,
    ( v3_pre_topc(sK1,sK0)
    | X0_45 != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) = X0_45 ),
    inference(resolution,[status(thm)],[c_2275,c_230])).

cnf(c_235,plain,
    ( X0_45 != X1_45
    | k2_pre_topc(X0_44,X0_45) = k2_pre_topc(X0_44,X1_45) ),
    theory(equality)).

cnf(c_242,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_237,plain,
    ( X0_45 != X1_45
    | k2_tops_1(X0_44,X0_45) = k2_tops_1(X0_44,X1_45) ),
    theory(equality)).

cnf(c_244,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_246,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k7_subset_1(u1_struct_0(X0_44),k2_pre_topc(X0_44,X0_45),k1_tops_1(X0_44,X0_45)) = k2_tops_1(X0_44,X0_45) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_270,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_281,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ sP3_iProver_split
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_284,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP2_iProver_split ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_1301,plain,
    ( X0_45 != X1_45
    | X0_45 = k1_tops_1(X0_44,X2_45)
    | k1_tops_1(X0_44,X2_45) != X1_45 ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_1302,plain,
    ( k1_tops_1(sK0,sK1) != sK1
    | sK1 = k1_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_993,plain,
    ( X0_45 != X1_45
    | k2_tops_1(sK0,sK1) != X1_45
    | k2_tops_1(sK0,sK1) = X0_45 ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_1159,plain,
    ( X0_45 != k2_tops_1(sK0,X1_45)
    | k2_tops_1(sK0,sK1) = X0_45
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,X1_45) ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_1415,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45)) != k2_tops_1(sK0,X0_45)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,X0_45) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_1417,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_930,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != X0_45
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) != X0_45 ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_1685,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45)) ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_1686,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_233,plain,
    ( X0_45 != X1_45
    | X2_45 != X3_45
    | k7_subset_1(X0_47,X0_45,X2_45) = k7_subset_1(X0_47,X1_45,X3_45) ),
    theory(equality)).

cnf(c_2666,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45))
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,X0_45)
    | sK1 != k1_tops_1(sK0,X0_45) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_2667,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1)
    | sK1 != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2666])).

cnf(c_2995,plain,
    ( X0_45 != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) = X0_45 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2626,c_17,c_16,c_15,c_242,c_244,c_246,c_270,c_227,c_281,c_284,c_208,c_1302,c_1417,c_1686,c_2667])).

cnf(c_3010,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[status(thm)],[c_2995,c_229])).

cnf(c_3030,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_6065,plain,
    ( v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5329,c_17,c_16,c_15,c_14,c_22,c_242,c_244,c_246,c_270,c_227,c_281,c_284,c_208,c_1302,c_1417,c_1686,c_2667])).

cnf(c_6070,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_737,c_6065])).

cnf(c_11398,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_11392,c_6070])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_221,plain,
    ( k3_xboole_0(X0_45,X1_45) = k3_xboole_0(X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_218,plain,
    ( r1_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X0_45,X1_45)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_722,plain,
    ( r1_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X0_45,X1_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_219,plain,
    ( ~ r1_xboole_0(X0_45,X1_45)
    | k4_xboole_0(X0_45,X1_45) = X0_45 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_721,plain,
    ( k4_xboole_0(X0_45,X1_45) = X0_45
    | r1_xboole_0(X0_45,X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_1368,plain,
    ( k4_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X0_45,X1_45)) = k3_xboole_0(X0_45,X1_45) ),
    inference(superposition,[status(thm)],[c_722,c_721])).

cnf(c_3304,plain,
    ( k4_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X1_45,X0_45)) = k3_xboole_0(X1_45,X0_45) ),
    inference(superposition,[status(thm)],[c_221,c_1368])).

cnf(c_11454,plain,
    ( k4_xboole_0(k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_11398,c_3304])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | r1_tarski(X0_45,k2_pre_topc(X0_44,X0_45))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_725,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | r1_tarski(X0_45,k2_pre_topc(X0_44,X0_45)) = iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_1379,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_725])).

cnf(c_263,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | r1_tarski(X0_45,k2_pre_topc(X0_44,X0_45)) = iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_265,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_1610,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1379,c_19,c_20,c_265])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_220,plain,
    ( ~ r1_tarski(X0_45,X1_45)
    | k3_xboole_0(X0_45,X1_45) = X0_45 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_720,plain,
    ( k3_xboole_0(X0_45,X1_45) = X0_45
    | r1_tarski(X0_45,X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_1615,plain,
    ( k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1610,c_720])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k7_subset_1(u1_struct_0(X0_44),X0_45,k2_tops_1(X0_44,X0_45)) = k1_tops_1(X0_44,X0_45) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_735,plain,
    ( k7_subset_1(u1_struct_0(X0_44),X0_45,k2_tops_1(X0_44,X0_45)) = k1_tops_1(X0_44,X0_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_2254,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_735])).

cnf(c_1223,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0_45) = k4_xboole_0(sK1,X0_45) ),
    inference(superposition,[status(thm)],[c_738,c_723])).

cnf(c_2264,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2254,c_1223])).

cnf(c_2693,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2264,c_19])).

cnf(c_3342,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_1615,c_3304])).

cnf(c_1127,plain,
    ( r1_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X1_45,X0_45)) = iProver_top ),
    inference(superposition,[status(thm)],[c_221,c_722])).

cnf(c_1617,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1615,c_1127])).

cnf(c_1706,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1617,c_721])).

cnf(c_3375,plain,
    ( k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3342,c_1706])).

cnf(c_11459,plain,
    ( k1_tops_1(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_11454,c_1615,c_2693,c_3375])).

cnf(c_9,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_212,plain,
    ( v3_pre_topc(X0_45,X0_44)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(X1_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X1_44)
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,X0_45) != X0_45 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_212])).

cnf(c_277,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_223,plain,
    ( v3_pre_topc(X0_45,X0_44)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v2_pre_topc(X0_44)
    | ~ l1_pre_topc(X0_44)
    | k1_tops_1(X0_44,X0_45) != X0_45
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_212])).

cnf(c_274,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP1_iProver_split
    | k1_tops_1(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_224,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_212])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11459,c_3030,c_3010,c_2813,c_208,c_277,c_274,c_224,c_15,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:24:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.94/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/0.97  
% 3.94/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.94/0.97  
% 3.94/0.97  ------  iProver source info
% 3.94/0.97  
% 3.94/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.94/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.94/0.97  git: non_committed_changes: false
% 3.94/0.97  git: last_make_outside_of_git: false
% 3.94/0.97  
% 3.94/0.97  ------ 
% 3.94/0.97  ------ Parsing...
% 3.94/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.94/0.97  
% 3.94/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.94/0.97  
% 3.94/0.97  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.94/0.97  
% 3.94/0.97  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.97  ------ Proving...
% 3.94/0.97  ------ Problem Properties 
% 3.94/0.97  
% 3.94/0.97  
% 3.94/0.97  clauses                                 22
% 3.94/0.97  conjectures                             5
% 3.94/0.97  EPR                                     4
% 3.94/0.97  Horn                                    19
% 3.94/0.97  unary                                   5
% 3.94/0.97  binary                                  7
% 3.94/0.97  lits                                    56
% 3.94/0.97  lits eq                                 10
% 3.94/0.97  fd_pure                                 0
% 3.94/0.97  fd_pseudo                               0
% 3.94/0.97  fd_cond                                 0
% 3.94/0.97  fd_pseudo_cond                          0
% 3.94/0.97  AC symbols                              0
% 3.94/0.97  
% 3.94/0.97  ------ Input Options Time Limit: Unbounded
% 3.94/0.97  
% 3.94/0.97  
% 3.94/0.97  ------ 
% 3.94/0.97  Current options:
% 3.94/0.97  ------ 
% 3.94/0.97  
% 3.94/0.97  
% 3.94/0.97  
% 3.94/0.97  
% 3.94/0.97  ------ Proving...
% 3.94/0.97  
% 3.94/0.97  
% 3.94/0.97  % SZS status Theorem for theBenchmark.p
% 3.94/0.97  
% 3.94/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.94/0.97  
% 3.94/0.97  fof(f13,conjecture,(
% 3.94/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f14,negated_conjecture,(
% 3.94/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1))))),
% 3.94/0.97    inference(negated_conjecture,[],[f13])).
% 3.94/0.97  
% 3.94/0.97  fof(f29,plain,(
% 3.94/0.97    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.94/0.97    inference(ennf_transformation,[],[f14])).
% 3.94/0.97  
% 3.94/0.97  fof(f30,plain,(
% 3.94/0.97    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.94/0.97    inference(flattening,[],[f29])).
% 3.94/0.97  
% 3.94/0.97  fof(f31,plain,(
% 3.94/0.97    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.94/0.97    inference(nnf_transformation,[],[f30])).
% 3.94/0.97  
% 3.94/0.97  fof(f32,plain,(
% 3.94/0.97    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.94/0.97    inference(flattening,[],[f31])).
% 3.94/0.97  
% 3.94/0.97  fof(f34,plain,(
% 3.94/0.97    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) != k2_tops_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),sK1) = k2_tops_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.94/0.97    introduced(choice_axiom,[])).
% 3.94/0.97  
% 3.94/0.97  fof(f33,plain,(
% 3.94/0.97    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) != k2_tops_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) = k2_tops_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) != k2_tops_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) = k2_tops_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.94/0.97    introduced(choice_axiom,[])).
% 3.94/0.97  
% 3.94/0.97  fof(f35,plain,(
% 3.94/0.97    ((k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.94/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 3.94/0.97  
% 3.94/0.97  fof(f51,plain,(
% 3.94/0.97    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.94/0.97    inference(cnf_transformation,[],[f35])).
% 3.94/0.97  
% 3.94/0.97  fof(f6,axiom,(
% 3.94/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f19,plain,(
% 3.94/0.97    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.94/0.97    inference(ennf_transformation,[],[f6])).
% 3.94/0.97  
% 3.94/0.97  fof(f20,plain,(
% 3.94/0.97    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.94/0.97    inference(flattening,[],[f19])).
% 3.94/0.97  
% 3.94/0.97  fof(f41,plain,(
% 3.94/0.97    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.94/0.97    inference(cnf_transformation,[],[f20])).
% 3.94/0.97  
% 3.94/0.97  fof(f5,axiom,(
% 3.94/0.97    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f18,plain,(
% 3.94/0.97    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.94/0.97    inference(ennf_transformation,[],[f5])).
% 3.94/0.97  
% 3.94/0.97  fof(f40,plain,(
% 3.94/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.94/0.97    inference(cnf_transformation,[],[f18])).
% 3.94/0.97  
% 3.94/0.97  fof(f50,plain,(
% 3.94/0.97    l1_pre_topc(sK0)),
% 3.94/0.97    inference(cnf_transformation,[],[f35])).
% 3.94/0.97  
% 3.94/0.97  fof(f52,plain,(
% 3.94/0.97    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 3.94/0.97    inference(cnf_transformation,[],[f35])).
% 3.94/0.97  
% 3.94/0.97  fof(f10,axiom,(
% 3.94/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f25,plain,(
% 3.94/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.94/0.97    inference(ennf_transformation,[],[f10])).
% 3.94/0.97  
% 3.94/0.97  fof(f26,plain,(
% 3.94/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.94/0.97    inference(flattening,[],[f25])).
% 3.94/0.97  
% 3.94/0.97  fof(f45,plain,(
% 3.94/0.97    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.94/0.97    inference(cnf_transformation,[],[f26])).
% 3.94/0.97  
% 3.94/0.97  fof(f49,plain,(
% 3.94/0.97    v2_pre_topc(sK0)),
% 3.94/0.97    inference(cnf_transformation,[],[f35])).
% 3.94/0.97  
% 3.94/0.97  fof(f53,plain,(
% 3.94/0.97    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.94/0.97    inference(cnf_transformation,[],[f35])).
% 3.94/0.97  
% 3.94/0.97  fof(f9,axiom,(
% 3.94/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f24,plain,(
% 3.94/0.97    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.97    inference(ennf_transformation,[],[f9])).
% 3.94/0.97  
% 3.94/0.97  fof(f44,plain,(
% 3.94/0.97    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.94/0.97    inference(cnf_transformation,[],[f24])).
% 3.94/0.97  
% 3.94/0.97  fof(f1,axiom,(
% 3.94/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f36,plain,(
% 3.94/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.94/0.97    inference(cnf_transformation,[],[f1])).
% 3.94/0.97  
% 3.94/0.97  fof(f4,axiom,(
% 3.94/0.97    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f39,plain,(
% 3.94/0.97    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 3.94/0.97    inference(cnf_transformation,[],[f4])).
% 3.94/0.97  
% 3.94/0.97  fof(f3,axiom,(
% 3.94/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f15,plain,(
% 3.94/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 3.94/0.97    inference(unused_predicate_definition_removal,[],[f3])).
% 3.94/0.97  
% 3.94/0.97  fof(f17,plain,(
% 3.94/0.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.94/0.97    inference(ennf_transformation,[],[f15])).
% 3.94/0.97  
% 3.94/0.97  fof(f38,plain,(
% 3.94/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.94/0.97    inference(cnf_transformation,[],[f17])).
% 3.94/0.97  
% 3.94/0.97  fof(f7,axiom,(
% 3.94/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f21,plain,(
% 3.94/0.97    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.97    inference(ennf_transformation,[],[f7])).
% 3.94/0.97  
% 3.94/0.97  fof(f42,plain,(
% 3.94/0.97    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.94/0.97    inference(cnf_transformation,[],[f21])).
% 3.94/0.97  
% 3.94/0.97  fof(f2,axiom,(
% 3.94/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f16,plain,(
% 3.94/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.94/0.97    inference(ennf_transformation,[],[f2])).
% 3.94/0.97  
% 3.94/0.97  fof(f37,plain,(
% 3.94/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.94/0.97    inference(cnf_transformation,[],[f16])).
% 3.94/0.97  
% 3.94/0.97  fof(f12,axiom,(
% 3.94/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.94/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.97  
% 3.94/0.97  fof(f28,plain,(
% 3.94/0.97    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.94/0.97    inference(ennf_transformation,[],[f12])).
% 3.94/0.97  
% 3.94/0.97  fof(f48,plain,(
% 3.94/0.97    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.94/0.97    inference(cnf_transformation,[],[f28])).
% 3.94/0.97  
% 3.94/0.97  fof(f46,plain,(
% 3.94/0.97    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.94/0.97    inference(cnf_transformation,[],[f26])).
% 3.94/0.97  
% 3.94/0.97  cnf(c_15,negated_conjecture,
% 3.94/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.94/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_206,negated_conjecture,
% 3.94/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_15]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_738,plain,
% 3.94/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_206]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_5,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.97      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.97      | ~ l1_pre_topc(X1) ),
% 3.94/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_216,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | m1_subset_1(k2_pre_topc(X0_44,X0_45),k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | ~ l1_pre_topc(X0_44) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_724,plain,
% 3.94/0.97      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | m1_subset_1(k2_pre_topc(X0_44,X0_45),k1_zfmisc_1(u1_struct_0(X0_44))) = iProver_top
% 3.94/0.97      | l1_pre_topc(X0_44) != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_4,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.94/0.97      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.94/0.97      inference(cnf_transformation,[],[f40]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_217,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_47))
% 3.94/0.97      | k7_subset_1(X0_47,X0_45,X1_45) = k4_xboole_0(X0_45,X1_45) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_723,plain,
% 3.94/0.97      ( k7_subset_1(X0_47,X0_45,X1_45) = k4_xboole_0(X0_45,X1_45)
% 3.94/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(X0_47)) != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1515,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(X0_44),k2_pre_topc(X0_44,X0_45),X1_45) = k4_xboole_0(k2_pre_topc(X0_44,X0_45),X1_45)
% 3.94/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | l1_pre_topc(X0_44) != iProver_top ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_724,c_723]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_10854,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0_45) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0_45)
% 3.94/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_738,c_1515]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_16,negated_conjecture,
% 3.94/0.97      ( l1_pre_topc(sK0) ),
% 3.94/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_19,plain,
% 3.94/0.97      ( l1_pre_topc(sK0) = iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_11392,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0_45) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0_45) ),
% 3.94/0.97      inference(global_propositional_subsumption,
% 3.94/0.97                [status(thm)],
% 3.94/0.97                [c_10854,c_19]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_14,negated_conjecture,
% 3.94/0.97      ( v3_pre_topc(sK1,sK0)
% 3.94/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_207,negated_conjecture,
% 3.94/0.97      ( v3_pre_topc(sK1,sK0)
% 3.94/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_14]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_737,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 3.94/0.97      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_10,plain,
% 3.94/0.97      ( ~ v3_pre_topc(X0,X1)
% 3.94/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.94/0.97      | ~ v2_pre_topc(X3)
% 3.94/0.97      | ~ l1_pre_topc(X3)
% 3.94/0.97      | ~ l1_pre_topc(X1)
% 3.94/0.97      | k1_tops_1(X1,X0) = X0 ),
% 3.94/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_211,plain,
% 3.94/0.97      ( ~ v3_pre_topc(X0_45,X0_44)
% 3.94/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(X1_44)))
% 3.94/0.97      | ~ v2_pre_topc(X1_44)
% 3.94/0.97      | ~ l1_pre_topc(X1_44)
% 3.94/0.97      | ~ l1_pre_topc(X0_44)
% 3.94/0.97      | k1_tops_1(X0_44,X0_45) = X0_45 ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_10]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_226,plain,
% 3.94/0.97      ( ~ v3_pre_topc(X0_45,X0_44)
% 3.94/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | ~ l1_pre_topc(X0_44)
% 3.94/0.97      | k1_tops_1(X0_44,X0_45) = X0_45
% 3.94/0.97      | ~ sP3_iProver_split ),
% 3.94/0.97      inference(splitting,
% 3.94/0.97                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 3.94/0.97                [c_211]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_732,plain,
% 3.94/0.97      ( k1_tops_1(X0_44,X0_45) = X0_45
% 3.94/0.97      | v3_pre_topc(X0_45,X0_44) != iProver_top
% 3.94/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | l1_pre_topc(X0_44) != iProver_top
% 3.94/0.97      | sP3_iProver_split != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_17,negated_conjecture,
% 3.94/0.97      ( v2_pre_topc(sK0) ),
% 3.94/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_18,plain,
% 3.94/0.97      ( v2_pre_topc(sK0) = iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_20,plain,
% 3.94/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_227,plain,
% 3.94/0.97      ( sP3_iProver_split | sP2_iProver_split ),
% 3.94/0.97      inference(splitting,
% 3.94/0.97                [splitting(split),new_symbols(definition,[])],
% 3.94/0.97                [c_211]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_279,plain,
% 3.94/0.97      ( sP3_iProver_split = iProver_top
% 3.94/0.97      | sP2_iProver_split = iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_280,plain,
% 3.94/0.97      ( k1_tops_1(X0_44,X0_45) = X0_45
% 3.94/0.97      | v3_pre_topc(X0_45,X0_44) != iProver_top
% 3.94/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | l1_pre_topc(X0_44) != iProver_top
% 3.94/0.97      | sP3_iProver_split != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_225,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | ~ v2_pre_topc(X0_44)
% 3.94/0.97      | ~ l1_pre_topc(X0_44)
% 3.94/0.97      | ~ sP2_iProver_split ),
% 3.94/0.97      inference(splitting,
% 3.94/0.97                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.94/0.97                [c_211]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_283,plain,
% 3.94/0.97      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | v2_pre_topc(X0_44) != iProver_top
% 3.94/0.97      | l1_pre_topc(X0_44) != iProver_top
% 3.94/0.97      | sP2_iProver_split != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_285,plain,
% 3.94/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.94/0.97      | v2_pre_topc(sK0) != iProver_top
% 3.94/0.97      | l1_pre_topc(sK0) != iProver_top
% 3.94/0.97      | sP2_iProver_split != iProver_top ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_283]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_5321,plain,
% 3.94/0.97      ( l1_pre_topc(X0_44) != iProver_top
% 3.94/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | v3_pre_topc(X0_45,X0_44) != iProver_top
% 3.94/0.97      | k1_tops_1(X0_44,X0_45) = X0_45 ),
% 3.94/0.97      inference(global_propositional_subsumption,
% 3.94/0.97                [status(thm)],
% 3.94/0.97                [c_732,c_18,c_19,c_20,c_279,c_280,c_285]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_5322,plain,
% 3.94/0.97      ( k1_tops_1(X0_44,X0_45) = X0_45
% 3.94/0.97      | v3_pre_topc(X0_45,X0_44) != iProver_top
% 3.94/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | l1_pre_topc(X0_44) != iProver_top ),
% 3.94/0.97      inference(renaming,[status(thm)],[c_5321]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_5329,plain,
% 3.94/0.97      ( k1_tops_1(sK0,sK1) = sK1
% 3.94/0.97      | v3_pre_topc(sK1,sK0) != iProver_top
% 3.94/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_738,c_5322]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_13,negated_conjecture,
% 3.94/0.97      ( ~ v3_pre_topc(sK1,sK0)
% 3.94/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_208,negated_conjecture,
% 3.94/0.97      ( ~ v3_pre_topc(sK1,sK0)
% 3.94/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_13]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_292,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
% 3.94/0.97      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_208]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_229,plain,( X0_45 = X0_45 ),theory(equality) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2813,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_229]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_230,plain,
% 3.94/0.97      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 3.94/0.97      theory(equality) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1246,plain,
% 3.94/0.97      ( X0_45 != X1_45 | X1_45 = X0_45 ),
% 3.94/0.97      inference(resolution,[status(thm)],[c_230,c_229]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2275,plain,
% 3.94/0.97      ( v3_pre_topc(sK1,sK0)
% 3.94/0.97      | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
% 3.94/0.97      inference(resolution,[status(thm)],[c_1246,c_207]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2626,plain,
% 3.94/0.97      ( v3_pre_topc(sK1,sK0)
% 3.94/0.97      | X0_45 != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
% 3.94/0.97      | k2_tops_1(sK0,sK1) = X0_45 ),
% 3.94/0.97      inference(resolution,[status(thm)],[c_2275,c_230]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_235,plain,
% 3.94/0.97      ( X0_45 != X1_45
% 3.94/0.97      | k2_pre_topc(X0_44,X0_45) = k2_pre_topc(X0_44,X1_45) ),
% 3.94/0.97      theory(equality) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_242,plain,
% 3.94/0.97      ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,sK1) | sK1 != sK1 ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_235]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_237,plain,
% 3.94/0.97      ( X0_45 != X1_45
% 3.94/0.97      | k2_tops_1(X0_44,X0_45) = k2_tops_1(X0_44,X1_45) ),
% 3.94/0.97      theory(equality) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_244,plain,
% 3.94/0.97      ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1) | sK1 != sK1 ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_237]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_246,plain,
% 3.94/0.97      ( sK1 = sK1 ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_229]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_8,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.97      | ~ l1_pre_topc(X1)
% 3.94/0.97      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.94/0.97      inference(cnf_transformation,[],[f44]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_213,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | ~ l1_pre_topc(X0_44)
% 3.94/0.97      | k7_subset_1(u1_struct_0(X0_44),k2_pre_topc(X0_44,X0_45),k1_tops_1(X0_44,X0_45)) = k2_tops_1(X0_44,X0_45) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_8]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_270,plain,
% 3.94/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.94/0.97      | ~ l1_pre_topc(sK0)
% 3.94/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_213]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_281,plain,
% 3.94/0.97      ( ~ v3_pre_topc(sK1,sK0)
% 3.94/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.94/0.97      | ~ l1_pre_topc(sK0)
% 3.94/0.97      | ~ sP3_iProver_split
% 3.94/0.97      | k1_tops_1(sK0,sK1) = sK1 ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_226]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_284,plain,
% 3.94/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.94/0.97      | ~ v2_pre_topc(sK0)
% 3.94/0.97      | ~ l1_pre_topc(sK0)
% 3.94/0.97      | ~ sP2_iProver_split ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_225]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1301,plain,
% 3.94/0.97      ( X0_45 != X1_45
% 3.94/0.97      | X0_45 = k1_tops_1(X0_44,X2_45)
% 3.94/0.97      | k1_tops_1(X0_44,X2_45) != X1_45 ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_230]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1302,plain,
% 3.94/0.97      ( k1_tops_1(sK0,sK1) != sK1
% 3.94/0.97      | sK1 = k1_tops_1(sK0,sK1)
% 3.94/0.97      | sK1 != sK1 ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_1301]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_993,plain,
% 3.94/0.97      ( X0_45 != X1_45
% 3.94/0.97      | k2_tops_1(sK0,sK1) != X1_45
% 3.94/0.97      | k2_tops_1(sK0,sK1) = X0_45 ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_230]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1159,plain,
% 3.94/0.97      ( X0_45 != k2_tops_1(sK0,X1_45)
% 3.94/0.97      | k2_tops_1(sK0,sK1) = X0_45
% 3.94/0.97      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,X1_45) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_993]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1415,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45)) != k2_tops_1(sK0,X0_45)
% 3.94/0.97      | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45))
% 3.94/0.97      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,X0_45) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_1159]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1417,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.94/0.97      | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
% 3.94/0.97      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_1415]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_930,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != X0_45
% 3.94/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 3.94/0.97      | k2_tops_1(sK0,sK1) != X0_45 ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_230]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1685,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45))
% 3.94/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 3.94/0.97      | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45)) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_930]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1686,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
% 3.94/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 3.94/0.97      | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_1685]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_233,plain,
% 3.94/0.97      ( X0_45 != X1_45
% 3.94/0.97      | X2_45 != X3_45
% 3.94/0.97      | k7_subset_1(X0_47,X0_45,X2_45) = k7_subset_1(X0_47,X1_45,X3_45) ),
% 3.94/0.97      theory(equality) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2666,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_45),k1_tops_1(sK0,X0_45))
% 3.94/0.97      | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,X0_45)
% 3.94/0.97      | sK1 != k1_tops_1(sK0,X0_45) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_233]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2667,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
% 3.94/0.97      | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1)
% 3.94/0.97      | sK1 != k1_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_2666]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2995,plain,
% 3.94/0.97      ( X0_45 != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
% 3.94/0.97      | k2_tops_1(sK0,sK1) = X0_45 ),
% 3.94/0.97      inference(global_propositional_subsumption,
% 3.94/0.97                [status(thm)],
% 3.94/0.97                [c_2626,c_17,c_16,c_15,c_242,c_244,c_246,c_270,c_227,
% 3.94/0.97                 c_281,c_284,c_208,c_1302,c_1417,c_1686,c_2667]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_3010,plain,
% 3.94/0.97      ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
% 3.94/0.97      inference(resolution,[status(thm)],[c_2995,c_229]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_3030,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
% 3.94/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 3.94/0.97      | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_930]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_6065,plain,
% 3.94/0.97      ( v3_pre_topc(sK1,sK0) != iProver_top ),
% 3.94/0.97      inference(global_propositional_subsumption,
% 3.94/0.97                [status(thm)],
% 3.94/0.97                [c_5329,c_17,c_16,c_15,c_14,c_22,c_242,c_244,c_246,c_270,
% 3.94/0.97                 c_227,c_281,c_284,c_208,c_1302,c_1417,c_1686,c_2667]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_6070,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_737,c_6065]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_11398,plain,
% 3.94/0.97      ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_11392,c_6070]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_0,plain,
% 3.94/0.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.94/0.97      inference(cnf_transformation,[],[f36]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_221,plain,
% 3.94/0.97      ( k3_xboole_0(X0_45,X1_45) = k3_xboole_0(X1_45,X0_45) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_3,plain,
% 3.94/0.97      ( r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 3.94/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_218,plain,
% 3.94/0.97      ( r1_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X0_45,X1_45)) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_722,plain,
% 3.94/0.97      ( r1_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X0_45,X1_45)) = iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2,plain,
% 3.94/0.97      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.94/0.97      inference(cnf_transformation,[],[f38]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_219,plain,
% 3.94/0.97      ( ~ r1_xboole_0(X0_45,X1_45) | k4_xboole_0(X0_45,X1_45) = X0_45 ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_2]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_721,plain,
% 3.94/0.97      ( k4_xboole_0(X0_45,X1_45) = X0_45
% 3.94/0.97      | r1_xboole_0(X0_45,X1_45) != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1368,plain,
% 3.94/0.97      ( k4_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X0_45,X1_45)) = k3_xboole_0(X0_45,X1_45) ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_722,c_721]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_3304,plain,
% 3.94/0.97      ( k4_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X1_45,X0_45)) = k3_xboole_0(X1_45,X0_45) ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_221,c_1368]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_11454,plain,
% 3.94/0.97      ( k4_xboole_0(k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_11398,c_3304]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_6,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.97      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.94/0.97      | ~ l1_pre_topc(X1) ),
% 3.94/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_215,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | r1_tarski(X0_45,k2_pre_topc(X0_44,X0_45))
% 3.94/0.97      | ~ l1_pre_topc(X0_44) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_6]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_725,plain,
% 3.94/0.97      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | r1_tarski(X0_45,k2_pre_topc(X0_44,X0_45)) = iProver_top
% 3.94/0.97      | l1_pre_topc(X0_44) != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1379,plain,
% 3.94/0.97      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
% 3.94/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_738,c_725]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_263,plain,
% 3.94/0.97      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | r1_tarski(X0_45,k2_pre_topc(X0_44,X0_45)) = iProver_top
% 3.94/0.97      | l1_pre_topc(X0_44) != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_265,plain,
% 3.94/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.94/0.97      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
% 3.94/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_263]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1610,plain,
% 3.94/0.97      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 3.94/0.97      inference(global_propositional_subsumption,
% 3.94/0.97                [status(thm)],
% 3.94/0.97                [c_1379,c_19,c_20,c_265]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1,plain,
% 3.94/0.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.94/0.97      inference(cnf_transformation,[],[f37]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_220,plain,
% 3.94/0.97      ( ~ r1_tarski(X0_45,X1_45) | k3_xboole_0(X0_45,X1_45) = X0_45 ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_1]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_720,plain,
% 3.94/0.97      ( k3_xboole_0(X0_45,X1_45) = X0_45
% 3.94/0.97      | r1_tarski(X0_45,X1_45) != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1615,plain,
% 3.94/0.97      ( k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = sK1 ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_1610,c_720]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_12,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.97      | ~ l1_pre_topc(X1)
% 3.94/0.97      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.94/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_209,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | ~ l1_pre_topc(X0_44)
% 3.94/0.97      | k7_subset_1(u1_struct_0(X0_44),X0_45,k2_tops_1(X0_44,X0_45)) = k1_tops_1(X0_44,X0_45) ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_12]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_735,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(X0_44),X0_45,k2_tops_1(X0_44,X0_45)) = k1_tops_1(X0_44,X0_45)
% 3.94/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.94/0.97      | l1_pre_topc(X0_44) != iProver_top ),
% 3.94/0.97      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2254,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 3.94/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_738,c_735]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1223,plain,
% 3.94/0.97      ( k7_subset_1(u1_struct_0(sK0),sK1,X0_45) = k4_xboole_0(sK1,X0_45) ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_738,c_723]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2264,plain,
% 3.94/0.97      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 3.94/0.97      | l1_pre_topc(sK0) != iProver_top ),
% 3.94/0.97      inference(demodulation,[status(thm)],[c_2254,c_1223]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_2693,plain,
% 3.94/0.97      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.94/0.97      inference(global_propositional_subsumption,
% 3.94/0.97                [status(thm)],
% 3.94/0.97                [c_2264,c_19]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_3342,plain,
% 3.94/0.97      ( k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_1615,c_3304]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1127,plain,
% 3.94/0.97      ( r1_xboole_0(k3_xboole_0(X0_45,X1_45),k4_xboole_0(X1_45,X0_45)) = iProver_top ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_221,c_722]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1617,plain,
% 3.94/0.97      ( r1_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = iProver_top ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_1615,c_1127]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_1706,plain,
% 3.94/0.97      ( k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = sK1 ),
% 3.94/0.97      inference(superposition,[status(thm)],[c_1617,c_721]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_3375,plain,
% 3.94/0.97      ( k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) = sK1 ),
% 3.94/0.97      inference(light_normalisation,[status(thm)],[c_3342,c_1706]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_11459,plain,
% 3.94/0.97      ( k1_tops_1(sK0,sK1) = sK1 ),
% 3.94/0.97      inference(light_normalisation,
% 3.94/0.97                [status(thm)],
% 3.94/0.97                [c_11454,c_1615,c_2693,c_3375]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_9,plain,
% 3.94/0.97      ( v3_pre_topc(X0,X1)
% 3.94/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.94/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.94/0.97      | ~ v2_pre_topc(X1)
% 3.94/0.97      | ~ l1_pre_topc(X1)
% 3.94/0.97      | ~ l1_pre_topc(X3)
% 3.94/0.97      | k1_tops_1(X1,X0) != X0 ),
% 3.94/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_212,plain,
% 3.94/0.97      ( v3_pre_topc(X0_45,X0_44)
% 3.94/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(X1_44)))
% 3.94/0.97      | ~ v2_pre_topc(X0_44)
% 3.94/0.97      | ~ l1_pre_topc(X1_44)
% 3.94/0.97      | ~ l1_pre_topc(X0_44)
% 3.94/0.97      | k1_tops_1(X0_44,X0_45) != X0_45 ),
% 3.94/0.97      inference(subtyping,[status(esa)],[c_9]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_222,plain,
% 3.94/0.97      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | ~ l1_pre_topc(X0_44)
% 3.94/0.97      | ~ sP0_iProver_split ),
% 3.94/0.97      inference(splitting,
% 3.94/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.94/0.97                [c_212]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_277,plain,
% 3.94/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.94/0.97      | ~ l1_pre_topc(sK0)
% 3.94/0.97      | ~ sP0_iProver_split ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_222]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_223,plain,
% 3.94/0.97      ( v3_pre_topc(X0_45,X0_44)
% 3.94/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.94/0.97      | ~ v2_pre_topc(X0_44)
% 3.94/0.97      | ~ l1_pre_topc(X0_44)
% 3.94/0.97      | k1_tops_1(X0_44,X0_45) != X0_45
% 3.94/0.97      | ~ sP1_iProver_split ),
% 3.94/0.97      inference(splitting,
% 3.94/0.97                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.94/0.97                [c_212]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_274,plain,
% 3.94/0.97      ( v3_pre_topc(sK1,sK0)
% 3.94/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.94/0.97      | ~ v2_pre_topc(sK0)
% 3.94/0.97      | ~ l1_pre_topc(sK0)
% 3.94/0.97      | ~ sP1_iProver_split
% 3.94/0.97      | k1_tops_1(sK0,sK1) != sK1 ),
% 3.94/0.97      inference(instantiation,[status(thm)],[c_223]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(c_224,plain,
% 3.94/0.97      ( sP1_iProver_split | sP0_iProver_split ),
% 3.94/0.97      inference(splitting,
% 3.94/0.97                [splitting(split),new_symbols(definition,[])],
% 3.94/0.97                [c_212]) ).
% 3.94/0.97  
% 3.94/0.97  cnf(contradiction,plain,
% 3.94/0.97      ( $false ),
% 3.94/0.97      inference(minisat,
% 3.94/0.97                [status(thm)],
% 3.94/0.97                [c_11459,c_3030,c_3010,c_2813,c_208,c_277,c_274,c_224,
% 3.94/0.97                 c_15,c_16,c_17]) ).
% 3.94/0.97  
% 3.94/0.97  
% 3.94/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.94/0.97  
% 3.94/0.97  ------                               Statistics
% 3.94/0.97  
% 3.94/0.97  ------ Selected
% 3.94/0.97  
% 3.94/0.97  total_time:                             0.39
% 3.94/0.97  
%------------------------------------------------------------------------------

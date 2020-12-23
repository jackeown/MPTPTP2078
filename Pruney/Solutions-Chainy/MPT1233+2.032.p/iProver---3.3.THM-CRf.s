%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:42 EST 2020

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 304 expanded)
%              Number of clauses        :   59 ( 109 expanded)
%              Number of leaves         :   17 (  64 expanded)
%              Depth                    :   19
%              Number of atoms          :  247 ( 729 expanded)
%              Number of equality atoms :   95 ( 249 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f53,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_337,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X0)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_338,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_2,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_555,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X1) ),
    inference(light_normalisation,[status(thm)],[c_338,c_2])).

cnf(c_865,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_555])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_536,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | v1_xboole_0(k1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_179,plain,
    ( ~ l1_pre_topc(X0)
    | v1_xboole_0(k1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_7,c_8])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_294,plain,
    ( v1_xboole_0(k1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_14])).

cnf(c_295,plain,
    ( v1_xboole_0(k1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_534,plain,
    ( v1_xboole_0(k1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_535,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_917,plain,
    ( k1_struct_0(sK0) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_534,c_535])).

cnf(c_935,plain,
    ( k1_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_536,c_917])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_168,plain,
    ( ~ l1_pre_topc(X0)
    | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_9])).

cnf(c_301,plain,
    ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_168,c_14])).

cnf(c_302,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_1005,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_935,c_302])).

cnf(c_1007,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1005,c_2])).

cnf(c_6,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_190,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_287,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_14])).

cnf(c_288,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_388,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | k2_struct_0(sK0) != X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_288,c_261])).

cnf(c_389,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)))) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_1013,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_1007,c_389])).

cnf(c_1336,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_865,c_1013])).

cnf(c_5,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_231,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_232,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_231])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_232,c_14])).

cnf(c_237,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_272,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_273,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(X0)
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(resolution,[status(thm)],[c_237,c_273])).

cnf(c_355,plain,
    ( ~ v1_xboole_0(X0)
    | k2_pre_topc(sK0,X0) = X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_318])).

cnf(c_356,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_360,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_0])).

cnf(c_442,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_588,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_589,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_713,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_588,c_589])).

cnf(c_1338,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1336,c_713])).

cnf(c_1339,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1338,c_2])).

cnf(c_13,negated_conjecture,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1014,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) != u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1007,c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1339,c_1014])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n004.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 17:24:53 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 1.36/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.36/0.96  
% 1.36/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.36/0.96  
% 1.36/0.96  ------  iProver source info
% 1.36/0.96  
% 1.36/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.36/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.36/0.96  git: non_committed_changes: false
% 1.36/0.96  git: last_make_outside_of_git: false
% 1.36/0.96  
% 1.36/0.96  ------ 
% 1.36/0.96  
% 1.36/0.96  ------ Input Options
% 1.36/0.96  
% 1.36/0.96  --out_options                           all
% 1.36/0.96  --tptp_safe_out                         true
% 1.36/0.96  --problem_path                          ""
% 1.36/0.96  --include_path                          ""
% 1.36/0.96  --clausifier                            res/vclausify_rel
% 1.36/0.96  --clausifier_options                    --mode clausify
% 1.36/0.96  --stdin                                 false
% 1.36/0.96  --stats_out                             all
% 1.36/0.96  
% 1.36/0.96  ------ General Options
% 1.36/0.96  
% 1.36/0.96  --fof                                   false
% 1.36/0.96  --time_out_real                         305.
% 1.36/0.96  --time_out_virtual                      -1.
% 1.36/0.96  --symbol_type_check                     false
% 1.36/0.96  --clausify_out                          false
% 1.36/0.96  --sig_cnt_out                           false
% 1.36/0.96  --trig_cnt_out                          false
% 1.36/0.96  --trig_cnt_out_tolerance                1.
% 1.36/0.96  --trig_cnt_out_sk_spl                   false
% 1.36/0.96  --abstr_cl_out                          false
% 1.36/0.96  
% 1.36/0.96  ------ Global Options
% 1.36/0.96  
% 1.36/0.96  --schedule                              default
% 1.36/0.96  --add_important_lit                     false
% 1.36/0.96  --prop_solver_per_cl                    1000
% 1.36/0.96  --min_unsat_core                        false
% 1.36/0.96  --soft_assumptions                      false
% 1.36/0.96  --soft_lemma_size                       3
% 1.36/0.96  --prop_impl_unit_size                   0
% 1.36/0.96  --prop_impl_unit                        []
% 1.36/0.96  --share_sel_clauses                     true
% 1.36/0.96  --reset_solvers                         false
% 1.36/0.96  --bc_imp_inh                            [conj_cone]
% 1.36/0.96  --conj_cone_tolerance                   3.
% 1.36/0.96  --extra_neg_conj                        none
% 1.36/0.96  --large_theory_mode                     true
% 1.36/0.96  --prolific_symb_bound                   200
% 1.36/0.96  --lt_threshold                          2000
% 1.36/0.96  --clause_weak_htbl                      true
% 1.36/0.96  --gc_record_bc_elim                     false
% 1.36/0.96  
% 1.36/0.96  ------ Preprocessing Options
% 1.36/0.96  
% 1.36/0.96  --preprocessing_flag                    true
% 1.36/0.96  --time_out_prep_mult                    0.1
% 1.36/0.96  --splitting_mode                        input
% 1.36/0.96  --splitting_grd                         true
% 1.36/0.96  --splitting_cvd                         false
% 1.36/0.96  --splitting_cvd_svl                     false
% 1.36/0.96  --splitting_nvd                         32
% 1.36/0.96  --sub_typing                            true
% 1.36/0.96  --prep_gs_sim                           true
% 1.36/0.96  --prep_unflatten                        true
% 1.36/0.96  --prep_res_sim                          true
% 1.36/0.96  --prep_upred                            true
% 1.36/0.96  --prep_sem_filter                       exhaustive
% 1.36/0.96  --prep_sem_filter_out                   false
% 1.36/0.96  --pred_elim                             true
% 1.36/0.96  --res_sim_input                         true
% 1.36/0.96  --eq_ax_congr_red                       true
% 1.36/0.96  --pure_diseq_elim                       true
% 1.36/0.96  --brand_transform                       false
% 1.36/0.96  --non_eq_to_eq                          false
% 1.36/0.96  --prep_def_merge                        true
% 1.36/0.96  --prep_def_merge_prop_impl              false
% 1.36/0.96  --prep_def_merge_mbd                    true
% 1.36/0.96  --prep_def_merge_tr_red                 false
% 1.36/0.96  --prep_def_merge_tr_cl                  false
% 1.36/0.96  --smt_preprocessing                     true
% 1.36/0.96  --smt_ac_axioms                         fast
% 1.36/0.96  --preprocessed_out                      false
% 1.36/0.96  --preprocessed_stats                    false
% 1.36/0.96  
% 1.36/0.96  ------ Abstraction refinement Options
% 1.36/0.96  
% 1.36/0.96  --abstr_ref                             []
% 1.36/0.96  --abstr_ref_prep                        false
% 1.36/0.96  --abstr_ref_until_sat                   false
% 1.36/0.96  --abstr_ref_sig_restrict                funpre
% 1.36/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.36/0.96  --abstr_ref_under                       []
% 1.36/0.96  
% 1.36/0.96  ------ SAT Options
% 1.36/0.96  
% 1.36/0.96  --sat_mode                              false
% 1.36/0.96  --sat_fm_restart_options                ""
% 1.36/0.96  --sat_gr_def                            false
% 1.36/0.96  --sat_epr_types                         true
% 1.36/0.96  --sat_non_cyclic_types                  false
% 1.36/0.96  --sat_finite_models                     false
% 1.36/0.96  --sat_fm_lemmas                         false
% 1.36/0.96  --sat_fm_prep                           false
% 1.36/0.96  --sat_fm_uc_incr                        true
% 1.36/0.96  --sat_out_model                         small
% 1.36/0.96  --sat_out_clauses                       false
% 1.36/0.96  
% 1.36/0.96  ------ QBF Options
% 1.36/0.96  
% 1.36/0.96  --qbf_mode                              false
% 1.36/0.96  --qbf_elim_univ                         false
% 1.36/0.96  --qbf_dom_inst                          none
% 1.36/0.96  --qbf_dom_pre_inst                      false
% 1.36/0.96  --qbf_sk_in                             false
% 1.36/0.96  --qbf_pred_elim                         true
% 1.36/0.96  --qbf_split                             512
% 1.36/0.96  
% 1.36/0.96  ------ BMC1 Options
% 1.36/0.96  
% 1.36/0.96  --bmc1_incremental                      false
% 1.36/0.96  --bmc1_axioms                           reachable_all
% 1.36/0.96  --bmc1_min_bound                        0
% 1.36/0.96  --bmc1_max_bound                        -1
% 1.36/0.96  --bmc1_max_bound_default                -1
% 1.36/0.96  --bmc1_symbol_reachability              true
% 1.36/0.96  --bmc1_property_lemmas                  false
% 1.36/0.96  --bmc1_k_induction                      false
% 1.36/0.96  --bmc1_non_equiv_states                 false
% 1.36/0.96  --bmc1_deadlock                         false
% 1.36/0.96  --bmc1_ucm                              false
% 1.36/0.96  --bmc1_add_unsat_core                   none
% 1.36/0.96  --bmc1_unsat_core_children              false
% 1.36/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.36/0.96  --bmc1_out_stat                         full
% 1.36/0.96  --bmc1_ground_init                      false
% 1.36/0.96  --bmc1_pre_inst_next_state              false
% 1.36/0.96  --bmc1_pre_inst_state                   false
% 1.36/0.96  --bmc1_pre_inst_reach_state             false
% 1.36/0.96  --bmc1_out_unsat_core                   false
% 1.36/0.96  --bmc1_aig_witness_out                  false
% 1.36/0.96  --bmc1_verbose                          false
% 1.36/0.96  --bmc1_dump_clauses_tptp                false
% 1.36/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.36/0.96  --bmc1_dump_file                        -
% 1.36/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.36/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.36/0.96  --bmc1_ucm_extend_mode                  1
% 1.36/0.96  --bmc1_ucm_init_mode                    2
% 1.36/0.96  --bmc1_ucm_cone_mode                    none
% 1.36/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.36/0.96  --bmc1_ucm_relax_model                  4
% 1.36/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.36/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.36/0.96  --bmc1_ucm_layered_model                none
% 1.36/0.96  --bmc1_ucm_max_lemma_size               10
% 1.36/0.96  
% 1.36/0.96  ------ AIG Options
% 1.36/0.96  
% 1.36/0.96  --aig_mode                              false
% 1.36/0.96  
% 1.36/0.96  ------ Instantiation Options
% 1.36/0.96  
% 1.36/0.96  --instantiation_flag                    true
% 1.36/0.96  --inst_sos_flag                         false
% 1.36/0.96  --inst_sos_phase                        true
% 1.36/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.36/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.36/0.96  --inst_lit_sel_side                     num_symb
% 1.36/0.96  --inst_solver_per_active                1400
% 1.36/0.96  --inst_solver_calls_frac                1.
% 1.36/0.96  --inst_passive_queue_type               priority_queues
% 1.36/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.36/0.96  --inst_passive_queues_freq              [25;2]
% 1.36/0.96  --inst_dismatching                      true
% 1.36/0.96  --inst_eager_unprocessed_to_passive     true
% 1.36/0.96  --inst_prop_sim_given                   true
% 1.36/0.96  --inst_prop_sim_new                     false
% 1.36/0.96  --inst_subs_new                         false
% 1.36/0.97  --inst_eq_res_simp                      false
% 1.36/0.97  --inst_subs_given                       false
% 1.36/0.97  --inst_orphan_elimination               true
% 1.36/0.97  --inst_learning_loop_flag               true
% 1.36/0.97  --inst_learning_start                   3000
% 1.36/0.97  --inst_learning_factor                  2
% 1.36/0.97  --inst_start_prop_sim_after_learn       3
% 1.36/0.97  --inst_sel_renew                        solver
% 1.36/0.97  --inst_lit_activity_flag                true
% 1.36/0.97  --inst_restr_to_given                   false
% 1.36/0.97  --inst_activity_threshold               500
% 1.36/0.97  --inst_out_proof                        true
% 1.36/0.97  
% 1.36/0.97  ------ Resolution Options
% 1.36/0.97  
% 1.36/0.97  --resolution_flag                       true
% 1.36/0.97  --res_lit_sel                           adaptive
% 1.36/0.97  --res_lit_sel_side                      none
% 1.36/0.97  --res_ordering                          kbo
% 1.36/0.97  --res_to_prop_solver                    active
% 1.36/0.97  --res_prop_simpl_new                    false
% 1.36/0.97  --res_prop_simpl_given                  true
% 1.36/0.97  --res_passive_queue_type                priority_queues
% 1.36/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.36/0.97  --res_passive_queues_freq               [15;5]
% 1.36/0.97  --res_forward_subs                      full
% 1.36/0.97  --res_backward_subs                     full
% 1.36/0.97  --res_forward_subs_resolution           true
% 1.36/0.97  --res_backward_subs_resolution          true
% 1.36/0.97  --res_orphan_elimination                true
% 1.36/0.97  --res_time_limit                        2.
% 1.36/0.97  --res_out_proof                         true
% 1.36/0.97  
% 1.36/0.97  ------ Superposition Options
% 1.36/0.97  
% 1.36/0.97  --superposition_flag                    true
% 1.36/0.97  --sup_passive_queue_type                priority_queues
% 1.36/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.36/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.36/0.97  --demod_completeness_check              fast
% 1.36/0.97  --demod_use_ground                      true
% 1.36/0.97  --sup_to_prop_solver                    passive
% 1.36/0.97  --sup_prop_simpl_new                    true
% 1.36/0.97  --sup_prop_simpl_given                  true
% 1.36/0.97  --sup_fun_splitting                     false
% 1.36/0.97  --sup_smt_interval                      50000
% 1.36/0.97  
% 1.36/0.97  ------ Superposition Simplification Setup
% 1.36/0.97  
% 1.36/0.97  --sup_indices_passive                   []
% 1.36/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.36/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.97  --sup_full_bw                           [BwDemod]
% 1.36/0.97  --sup_immed_triv                        [TrivRules]
% 1.36/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.36/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.97  --sup_immed_bw_main                     []
% 1.36/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.36/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.36/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.36/0.97  
% 1.36/0.97  ------ Combination Options
% 1.36/0.97  
% 1.36/0.97  --comb_res_mult                         3
% 1.36/0.97  --comb_sup_mult                         2
% 1.36/0.97  --comb_inst_mult                        10
% 1.36/0.97  
% 1.36/0.97  ------ Debug Options
% 1.36/0.97  
% 1.36/0.97  --dbg_backtrace                         false
% 1.36/0.97  --dbg_dump_prop_clauses                 false
% 1.36/0.97  --dbg_dump_prop_clauses_file            -
% 1.36/0.97  --dbg_out_stat                          false
% 1.36/0.97  ------ Parsing...
% 1.36/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.36/0.97  
% 1.36/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.36/0.97  
% 1.36/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.36/0.97  
% 1.36/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.36/0.97  ------ Proving...
% 1.36/0.97  ------ Problem Properties 
% 1.36/0.97  
% 1.36/0.97  
% 1.36/0.97  clauses                                 12
% 1.36/0.97  conjectures                             1
% 1.36/0.97  EPR                                     2
% 1.36/0.97  Horn                                    12
% 1.36/0.97  unary                                   6
% 1.36/0.97  binary                                  5
% 1.36/0.97  lits                                    19
% 1.36/0.97  lits eq                                 14
% 1.36/0.97  fd_pure                                 0
% 1.36/0.97  fd_pseudo                               0
% 1.36/0.97  fd_cond                                 0
% 1.36/0.97  fd_pseudo_cond                          1
% 1.36/0.97  AC symbols                              0
% 1.36/0.97  
% 1.36/0.97  ------ Schedule dynamic 5 is on 
% 1.36/0.97  
% 1.36/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.36/0.97  
% 1.36/0.97  
% 1.36/0.97  ------ 
% 1.36/0.97  Current options:
% 1.36/0.97  ------ 
% 1.36/0.97  
% 1.36/0.97  ------ Input Options
% 1.36/0.97  
% 1.36/0.97  --out_options                           all
% 1.36/0.97  --tptp_safe_out                         true
% 1.36/0.97  --problem_path                          ""
% 1.36/0.97  --include_path                          ""
% 1.36/0.97  --clausifier                            res/vclausify_rel
% 1.36/0.97  --clausifier_options                    --mode clausify
% 1.36/0.97  --stdin                                 false
% 1.36/0.97  --stats_out                             all
% 1.36/0.97  
% 1.36/0.97  ------ General Options
% 1.36/0.97  
% 1.36/0.97  --fof                                   false
% 1.36/0.97  --time_out_real                         305.
% 1.36/0.97  --time_out_virtual                      -1.
% 1.36/0.97  --symbol_type_check                     false
% 1.36/0.97  --clausify_out                          false
% 1.36/0.97  --sig_cnt_out                           false
% 1.36/0.97  --trig_cnt_out                          false
% 1.36/0.97  --trig_cnt_out_tolerance                1.
% 1.36/0.97  --trig_cnt_out_sk_spl                   false
% 1.36/0.97  --abstr_cl_out                          false
% 1.36/0.97  
% 1.36/0.97  ------ Global Options
% 1.36/0.97  
% 1.36/0.97  --schedule                              default
% 1.36/0.97  --add_important_lit                     false
% 1.36/0.97  --prop_solver_per_cl                    1000
% 1.36/0.97  --min_unsat_core                        false
% 1.36/0.97  --soft_assumptions                      false
% 1.36/0.97  --soft_lemma_size                       3
% 1.36/0.97  --prop_impl_unit_size                   0
% 1.36/0.97  --prop_impl_unit                        []
% 1.36/0.97  --share_sel_clauses                     true
% 1.36/0.97  --reset_solvers                         false
% 1.36/0.97  --bc_imp_inh                            [conj_cone]
% 1.36/0.97  --conj_cone_tolerance                   3.
% 1.36/0.97  --extra_neg_conj                        none
% 1.36/0.97  --large_theory_mode                     true
% 1.36/0.97  --prolific_symb_bound                   200
% 1.36/0.97  --lt_threshold                          2000
% 1.36/0.97  --clause_weak_htbl                      true
% 1.36/0.97  --gc_record_bc_elim                     false
% 1.36/0.97  
% 1.36/0.97  ------ Preprocessing Options
% 1.36/0.97  
% 1.36/0.97  --preprocessing_flag                    true
% 1.36/0.97  --time_out_prep_mult                    0.1
% 1.36/0.97  --splitting_mode                        input
% 1.36/0.97  --splitting_grd                         true
% 1.36/0.97  --splitting_cvd                         false
% 1.36/0.97  --splitting_cvd_svl                     false
% 1.36/0.97  --splitting_nvd                         32
% 1.36/0.97  --sub_typing                            true
% 1.36/0.97  --prep_gs_sim                           true
% 1.36/0.97  --prep_unflatten                        true
% 1.36/0.97  --prep_res_sim                          true
% 1.36/0.97  --prep_upred                            true
% 1.36/0.97  --prep_sem_filter                       exhaustive
% 1.36/0.97  --prep_sem_filter_out                   false
% 1.36/0.97  --pred_elim                             true
% 1.36/0.97  --res_sim_input                         true
% 1.36/0.97  --eq_ax_congr_red                       true
% 1.36/0.97  --pure_diseq_elim                       true
% 1.36/0.97  --brand_transform                       false
% 1.36/0.97  --non_eq_to_eq                          false
% 1.36/0.97  --prep_def_merge                        true
% 1.36/0.97  --prep_def_merge_prop_impl              false
% 1.36/0.97  --prep_def_merge_mbd                    true
% 1.36/0.97  --prep_def_merge_tr_red                 false
% 1.36/0.97  --prep_def_merge_tr_cl                  false
% 1.36/0.97  --smt_preprocessing                     true
% 1.36/0.97  --smt_ac_axioms                         fast
% 1.36/0.97  --preprocessed_out                      false
% 1.36/0.97  --preprocessed_stats                    false
% 1.36/0.97  
% 1.36/0.97  ------ Abstraction refinement Options
% 1.36/0.97  
% 1.36/0.97  --abstr_ref                             []
% 1.36/0.97  --abstr_ref_prep                        false
% 1.36/0.97  --abstr_ref_until_sat                   false
% 1.36/0.97  --abstr_ref_sig_restrict                funpre
% 1.36/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.36/0.97  --abstr_ref_under                       []
% 1.36/0.97  
% 1.36/0.97  ------ SAT Options
% 1.36/0.97  
% 1.36/0.97  --sat_mode                              false
% 1.36/0.97  --sat_fm_restart_options                ""
% 1.36/0.97  --sat_gr_def                            false
% 1.36/0.97  --sat_epr_types                         true
% 1.36/0.97  --sat_non_cyclic_types                  false
% 1.36/0.97  --sat_finite_models                     false
% 1.36/0.97  --sat_fm_lemmas                         false
% 1.36/0.97  --sat_fm_prep                           false
% 1.36/0.97  --sat_fm_uc_incr                        true
% 1.36/0.97  --sat_out_model                         small
% 1.36/0.97  --sat_out_clauses                       false
% 1.36/0.97  
% 1.36/0.97  ------ QBF Options
% 1.36/0.97  
% 1.36/0.97  --qbf_mode                              false
% 1.36/0.97  --qbf_elim_univ                         false
% 1.36/0.97  --qbf_dom_inst                          none
% 1.36/0.97  --qbf_dom_pre_inst                      false
% 1.36/0.97  --qbf_sk_in                             false
% 1.36/0.97  --qbf_pred_elim                         true
% 1.36/0.97  --qbf_split                             512
% 1.36/0.97  
% 1.36/0.97  ------ BMC1 Options
% 1.36/0.97  
% 1.36/0.97  --bmc1_incremental                      false
% 1.36/0.97  --bmc1_axioms                           reachable_all
% 1.36/0.97  --bmc1_min_bound                        0
% 1.36/0.97  --bmc1_max_bound                        -1
% 1.36/0.97  --bmc1_max_bound_default                -1
% 1.36/0.97  --bmc1_symbol_reachability              true
% 1.36/0.97  --bmc1_property_lemmas                  false
% 1.36/0.97  --bmc1_k_induction                      false
% 1.36/0.97  --bmc1_non_equiv_states                 false
% 1.36/0.97  --bmc1_deadlock                         false
% 1.36/0.97  --bmc1_ucm                              false
% 1.36/0.97  --bmc1_add_unsat_core                   none
% 1.36/0.97  --bmc1_unsat_core_children              false
% 1.36/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.36/0.97  --bmc1_out_stat                         full
% 1.36/0.97  --bmc1_ground_init                      false
% 1.36/0.97  --bmc1_pre_inst_next_state              false
% 1.36/0.97  --bmc1_pre_inst_state                   false
% 1.36/0.97  --bmc1_pre_inst_reach_state             false
% 1.36/0.97  --bmc1_out_unsat_core                   false
% 1.36/0.97  --bmc1_aig_witness_out                  false
% 1.36/0.97  --bmc1_verbose                          false
% 1.36/0.97  --bmc1_dump_clauses_tptp                false
% 1.36/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.36/0.97  --bmc1_dump_file                        -
% 1.36/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.36/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.36/0.97  --bmc1_ucm_extend_mode                  1
% 1.36/0.97  --bmc1_ucm_init_mode                    2
% 1.36/0.97  --bmc1_ucm_cone_mode                    none
% 1.36/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.36/0.97  --bmc1_ucm_relax_model                  4
% 1.36/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.36/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.36/0.97  --bmc1_ucm_layered_model                none
% 1.36/0.97  --bmc1_ucm_max_lemma_size               10
% 1.36/0.97  
% 1.36/0.97  ------ AIG Options
% 1.36/0.97  
% 1.36/0.97  --aig_mode                              false
% 1.36/0.97  
% 1.36/0.97  ------ Instantiation Options
% 1.36/0.97  
% 1.36/0.97  --instantiation_flag                    true
% 1.36/0.97  --inst_sos_flag                         false
% 1.36/0.97  --inst_sos_phase                        true
% 1.36/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.36/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.36/0.97  --inst_lit_sel_side                     none
% 1.36/0.97  --inst_solver_per_active                1400
% 1.36/0.97  --inst_solver_calls_frac                1.
% 1.36/0.97  --inst_passive_queue_type               priority_queues
% 1.36/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.36/0.97  --inst_passive_queues_freq              [25;2]
% 1.36/0.97  --inst_dismatching                      true
% 1.36/0.97  --inst_eager_unprocessed_to_passive     true
% 1.36/0.97  --inst_prop_sim_given                   true
% 1.36/0.97  --inst_prop_sim_new                     false
% 1.36/0.97  --inst_subs_new                         false
% 1.36/0.97  --inst_eq_res_simp                      false
% 1.36/0.97  --inst_subs_given                       false
% 1.36/0.97  --inst_orphan_elimination               true
% 1.36/0.97  --inst_learning_loop_flag               true
% 1.36/0.97  --inst_learning_start                   3000
% 1.36/0.97  --inst_learning_factor                  2
% 1.36/0.97  --inst_start_prop_sim_after_learn       3
% 1.36/0.97  --inst_sel_renew                        solver
% 1.36/0.97  --inst_lit_activity_flag                true
% 1.36/0.97  --inst_restr_to_given                   false
% 1.36/0.97  --inst_activity_threshold               500
% 1.36/0.97  --inst_out_proof                        true
% 1.36/0.97  
% 1.36/0.97  ------ Resolution Options
% 1.36/0.97  
% 1.36/0.97  --resolution_flag                       false
% 1.36/0.97  --res_lit_sel                           adaptive
% 1.36/0.97  --res_lit_sel_side                      none
% 1.36/0.97  --res_ordering                          kbo
% 1.36/0.97  --res_to_prop_solver                    active
% 1.36/0.97  --res_prop_simpl_new                    false
% 1.36/0.97  --res_prop_simpl_given                  true
% 1.36/0.97  --res_passive_queue_type                priority_queues
% 1.36/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.36/0.97  --res_passive_queues_freq               [15;5]
% 1.36/0.97  --res_forward_subs                      full
% 1.36/0.97  --res_backward_subs                     full
% 1.36/0.97  --res_forward_subs_resolution           true
% 1.36/0.97  --res_backward_subs_resolution          true
% 1.36/0.97  --res_orphan_elimination                true
% 1.36/0.97  --res_time_limit                        2.
% 1.36/0.97  --res_out_proof                         true
% 1.36/0.97  
% 1.36/0.97  ------ Superposition Options
% 1.36/0.97  
% 1.36/0.97  --superposition_flag                    true
% 1.36/0.97  --sup_passive_queue_type                priority_queues
% 1.36/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.36/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.36/0.97  --demod_completeness_check              fast
% 1.36/0.97  --demod_use_ground                      true
% 1.36/0.97  --sup_to_prop_solver                    passive
% 1.36/0.97  --sup_prop_simpl_new                    true
% 1.36/0.97  --sup_prop_simpl_given                  true
% 1.36/0.97  --sup_fun_splitting                     false
% 1.36/0.97  --sup_smt_interval                      50000
% 1.36/0.97  
% 1.36/0.97  ------ Superposition Simplification Setup
% 1.36/0.97  
% 1.36/0.97  --sup_indices_passive                   []
% 1.36/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.36/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.97  --sup_full_bw                           [BwDemod]
% 1.36/0.97  --sup_immed_triv                        [TrivRules]
% 1.36/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.36/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.97  --sup_immed_bw_main                     []
% 1.36/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.36/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.36/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.36/0.97  
% 1.36/0.97  ------ Combination Options
% 1.36/0.97  
% 1.36/0.97  --comb_res_mult                         3
% 1.36/0.97  --comb_sup_mult                         2
% 1.36/0.97  --comb_inst_mult                        10
% 1.36/0.97  
% 1.36/0.97  ------ Debug Options
% 1.36/0.97  
% 1.36/0.97  --dbg_backtrace                         false
% 1.36/0.97  --dbg_dump_prop_clauses                 false
% 1.36/0.97  --dbg_dump_prop_clauses_file            -
% 1.36/0.97  --dbg_out_stat                          false
% 1.36/0.97  
% 1.36/0.97  
% 1.36/0.97  
% 1.36/0.97  
% 1.36/0.97  ------ Proving...
% 1.36/0.97  
% 1.36/0.97  
% 1.36/0.97  % SZS status Theorem for theBenchmark.p
% 1.36/0.97  
% 1.36/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.36/0.97  
% 1.36/0.97  fof(f5,axiom,(
% 1.36/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f20,plain,(
% 1.36/0.97    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.97    inference(ennf_transformation,[],[f5])).
% 1.36/0.97  
% 1.36/0.97  fof(f38,plain,(
% 1.36/0.97    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.36/0.97    inference(cnf_transformation,[],[f20])).
% 1.36/0.97  
% 1.36/0.97  fof(f7,axiom,(
% 1.36/0.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f40,plain,(
% 1.36/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.36/0.97    inference(cnf_transformation,[],[f7])).
% 1.36/0.97  
% 1.36/0.97  fof(f4,axiom,(
% 1.36/0.97    ! [X0] : k2_subset_1(X0) = X0),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f37,plain,(
% 1.36/0.97    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.36/0.97    inference(cnf_transformation,[],[f4])).
% 1.36/0.97  
% 1.36/0.97  fof(f6,axiom,(
% 1.36/0.97    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f39,plain,(
% 1.36/0.97    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.36/0.97    inference(cnf_transformation,[],[f6])).
% 1.36/0.97  
% 1.36/0.97  fof(f3,axiom,(
% 1.36/0.97    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f36,plain,(
% 1.36/0.97    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.36/0.97    inference(cnf_transformation,[],[f3])).
% 1.36/0.97  
% 1.36/0.97  fof(f52,plain,(
% 1.36/0.97    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.36/0.97    inference(definition_unfolding,[],[f39,f36])).
% 1.36/0.97  
% 1.36/0.97  fof(f53,plain,(
% 1.36/0.97    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.36/0.97    inference(definition_unfolding,[],[f37,f52])).
% 1.36/0.97  
% 1.36/0.97  fof(f1,axiom,(
% 1.36/0.97    v1_xboole_0(k1_xboole_0)),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f34,plain,(
% 1.36/0.97    v1_xboole_0(k1_xboole_0)),
% 1.36/0.97    inference(cnf_transformation,[],[f1])).
% 1.36/0.97  
% 1.36/0.97  fof(f11,axiom,(
% 1.36/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f24,plain,(
% 1.36/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.36/0.97    inference(ennf_transformation,[],[f11])).
% 1.36/0.97  
% 1.36/0.97  fof(f43,plain,(
% 1.36/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.36/0.97    inference(cnf_transformation,[],[f24])).
% 1.36/0.97  
% 1.36/0.97  fof(f12,axiom,(
% 1.36/0.97    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f25,plain,(
% 1.36/0.97    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.36/0.97    inference(ennf_transformation,[],[f12])).
% 1.36/0.97  
% 1.36/0.97  fof(f44,plain,(
% 1.36/0.97    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.36/0.97    inference(cnf_transformation,[],[f25])).
% 1.36/0.97  
% 1.36/0.97  fof(f16,conjecture,(
% 1.36/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f17,negated_conjecture,(
% 1.36/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.36/0.97    inference(negated_conjecture,[],[f16])).
% 1.36/0.97  
% 1.36/0.97  fof(f30,plain,(
% 1.36/0.97    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.36/0.97    inference(ennf_transformation,[],[f17])).
% 1.36/0.97  
% 1.36/0.97  fof(f31,plain,(
% 1.36/0.97    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.36/0.97    inference(flattening,[],[f30])).
% 1.36/0.97  
% 1.36/0.97  fof(f32,plain,(
% 1.36/0.97    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.36/0.97    introduced(choice_axiom,[])).
% 1.36/0.97  
% 1.36/0.97  fof(f33,plain,(
% 1.36/0.97    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.36/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 1.36/0.97  
% 1.36/0.97  fof(f50,plain,(
% 1.36/0.97    l1_pre_topc(sK0)),
% 1.36/0.97    inference(cnf_transformation,[],[f33])).
% 1.36/0.97  
% 1.36/0.97  fof(f2,axiom,(
% 1.36/0.97    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f19,plain,(
% 1.36/0.97    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.36/0.97    inference(ennf_transformation,[],[f2])).
% 1.36/0.97  
% 1.36/0.97  fof(f35,plain,(
% 1.36/0.97    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.36/0.97    inference(cnf_transformation,[],[f19])).
% 1.36/0.97  
% 1.36/0.97  fof(f13,axiom,(
% 1.36/0.97    ! [X0] : (l1_struct_0(X0) => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f26,plain,(
% 1.36/0.97    ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.36/0.97    inference(ennf_transformation,[],[f13])).
% 1.36/0.97  
% 1.36/0.97  fof(f45,plain,(
% 1.36/0.97    ( ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.36/0.97    inference(cnf_transformation,[],[f26])).
% 1.36/0.97  
% 1.36/0.97  fof(f10,axiom,(
% 1.36/0.97    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f23,plain,(
% 1.36/0.97    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.36/0.97    inference(ennf_transformation,[],[f10])).
% 1.36/0.97  
% 1.36/0.97  fof(f42,plain,(
% 1.36/0.97    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.36/0.97    inference(cnf_transformation,[],[f23])).
% 1.36/0.97  
% 1.36/0.97  fof(f15,axiom,(
% 1.36/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f29,plain,(
% 1.36/0.97    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.97    inference(ennf_transformation,[],[f15])).
% 1.36/0.97  
% 1.36/0.97  fof(f48,plain,(
% 1.36/0.97    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.36/0.97    inference(cnf_transformation,[],[f29])).
% 1.36/0.97  
% 1.36/0.97  fof(f9,axiom,(
% 1.36/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f21,plain,(
% 1.36/0.97    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.36/0.97    inference(ennf_transformation,[],[f9])).
% 1.36/0.97  
% 1.36/0.97  fof(f22,plain,(
% 1.36/0.97    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.36/0.97    inference(flattening,[],[f21])).
% 1.36/0.97  
% 1.36/0.97  fof(f41,plain,(
% 1.36/0.97    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.36/0.97    inference(cnf_transformation,[],[f22])).
% 1.36/0.97  
% 1.36/0.97  fof(f49,plain,(
% 1.36/0.97    v2_pre_topc(sK0)),
% 1.36/0.97    inference(cnf_transformation,[],[f33])).
% 1.36/0.97  
% 1.36/0.97  fof(f14,axiom,(
% 1.36/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.36/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.36/0.97  
% 1.36/0.97  fof(f27,plain,(
% 1.36/0.97    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.97    inference(ennf_transformation,[],[f14])).
% 1.36/0.97  
% 1.36/0.97  fof(f28,plain,(
% 1.36/0.97    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.97    inference(flattening,[],[f27])).
% 1.36/0.97  
% 1.36/0.97  fof(f46,plain,(
% 1.36/0.97    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.36/0.97    inference(cnf_transformation,[],[f28])).
% 1.36/0.97  
% 1.36/0.97  fof(f51,plain,(
% 1.36/0.97    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.36/0.97    inference(cnf_transformation,[],[f33])).
% 1.36/0.97  
% 1.36/0.97  cnf(c_3,plain,
% 1.36/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.36/0.97      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 1.36/0.97      inference(cnf_transformation,[],[f38]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_4,plain,
% 1.36/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.36/0.97      inference(cnf_transformation,[],[f40]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_337,plain,
% 1.36/0.97      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 1.36/0.97      | k1_zfmisc_1(X2) != k1_zfmisc_1(X0)
% 1.36/0.97      | k1_xboole_0 != X1 ),
% 1.36/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_338,plain,
% 1.36/0.97      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0
% 1.36/0.97      | k1_zfmisc_1(X1) != k1_zfmisc_1(X0) ),
% 1.36/0.97      inference(unflattening,[status(thm)],[c_337]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_2,plain,
% 1.36/0.97      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 1.36/0.97      inference(cnf_transformation,[],[f53]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_555,plain,
% 1.36/0.97      ( k3_subset_1(X0,X0) = k1_xboole_0
% 1.36/0.97      | k1_zfmisc_1(X0) != k1_zfmisc_1(X1) ),
% 1.36/0.97      inference(light_normalisation,[status(thm)],[c_338,c_2]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_865,plain,
% 1.36/0.97      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 1.36/0.97      inference(equality_resolution,[status(thm)],[c_555]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_0,plain,
% 1.36/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 1.36/0.97      inference(cnf_transformation,[],[f34]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_536,plain,
% 1.36/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.36/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_7,plain,
% 1.36/0.97      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.36/0.97      inference(cnf_transformation,[],[f43]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_8,plain,
% 1.36/0.97      ( ~ l1_struct_0(X0) | v1_xboole_0(k1_struct_0(X0)) ),
% 1.36/0.97      inference(cnf_transformation,[],[f44]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_179,plain,
% 1.36/0.97      ( ~ l1_pre_topc(X0) | v1_xboole_0(k1_struct_0(X0)) ),
% 1.36/0.97      inference(resolution,[status(thm)],[c_7,c_8]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_14,negated_conjecture,
% 1.36/0.97      ( l1_pre_topc(sK0) ),
% 1.36/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_294,plain,
% 1.36/0.97      ( v1_xboole_0(k1_struct_0(X0)) | sK0 != X0 ),
% 1.36/0.97      inference(resolution_lifted,[status(thm)],[c_179,c_14]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_295,plain,
% 1.36/0.97      ( v1_xboole_0(k1_struct_0(sK0)) ),
% 1.36/0.97      inference(unflattening,[status(thm)],[c_294]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_534,plain,
% 1.36/0.97      ( v1_xboole_0(k1_struct_0(sK0)) = iProver_top ),
% 1.36/0.97      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_1,plain,
% 1.36/0.97      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 1.36/0.97      inference(cnf_transformation,[],[f35]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_535,plain,
% 1.36/0.97      ( X0 = X1
% 1.36/0.97      | v1_xboole_0(X1) != iProver_top
% 1.36/0.97      | v1_xboole_0(X0) != iProver_top ),
% 1.36/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_917,plain,
% 1.36/0.97      ( k1_struct_0(sK0) = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.36/0.97      inference(superposition,[status(thm)],[c_534,c_535]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_935,plain,
% 1.36/0.97      ( k1_struct_0(sK0) = k1_xboole_0 ),
% 1.36/0.97      inference(superposition,[status(thm)],[c_536,c_917]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_9,plain,
% 1.36/0.97      ( ~ l1_struct_0(X0)
% 1.36/0.97      | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
% 1.36/0.97      inference(cnf_transformation,[],[f45]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_168,plain,
% 1.36/0.97      ( ~ l1_pre_topc(X0)
% 1.36/0.97      | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
% 1.36/0.97      inference(resolution,[status(thm)],[c_7,c_9]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_301,plain,
% 1.36/0.97      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
% 1.36/0.97      | sK0 != X0 ),
% 1.36/0.97      inference(resolution_lifted,[status(thm)],[c_168,c_14]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_302,plain,
% 1.36/0.97      ( k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) = k2_struct_0(sK0) ),
% 1.36/0.97      inference(unflattening,[status(thm)],[c_301]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_1005,plain,
% 1.36/0.97      ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
% 1.36/0.97      inference(demodulation,[status(thm)],[c_935,c_302]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_1007,plain,
% 1.36/0.97      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.36/0.97      inference(demodulation,[status(thm)],[c_1005,c_2]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_6,plain,
% 1.36/0.97      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.36/0.97      | ~ l1_struct_0(X0) ),
% 1.36/0.97      inference(cnf_transformation,[],[f42]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_190,plain,
% 1.36/0.97      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.36/0.97      | ~ l1_pre_topc(X0) ),
% 1.36/0.97      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_287,plain,
% 1.36/0.97      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.36/0.97      | sK0 != X0 ),
% 1.36/0.97      inference(resolution_lifted,[status(thm)],[c_190,c_14]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_288,plain,
% 1.36/0.97      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.36/0.97      inference(unflattening,[status(thm)],[c_287]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_12,plain,
% 1.36/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.36/0.97      | ~ l1_pre_topc(X1)
% 1.36/0.97      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 1.36/0.97      inference(cnf_transformation,[],[f48]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_260,plain,
% 1.36/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.36/0.97      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 1.36/0.97      | sK0 != X1 ),
% 1.36/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_261,plain,
% 1.36/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.36/0.97      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 1.36/0.97      inference(unflattening,[status(thm)],[c_260]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_388,plain,
% 1.36/0.97      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 1.36/0.97      | k2_struct_0(sK0) != X0
% 1.36/0.97      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.36/0.97      inference(resolution_lifted,[status(thm)],[c_288,c_261]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_389,plain,
% 1.36/0.97      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)))) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
% 1.36/0.97      inference(unflattening,[status(thm)],[c_388]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_1013,plain,
% 1.36/0.97      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
% 1.36/0.97      inference(demodulation,[status(thm)],[c_1007,c_389]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_1336,plain,
% 1.36/0.97      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
% 1.36/0.97      inference(demodulation,[status(thm)],[c_865,c_1013]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_5,plain,
% 1.36/0.97      ( v4_pre_topc(X0,X1)
% 1.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.36/0.97      | ~ v2_pre_topc(X1)
% 1.36/0.97      | ~ l1_pre_topc(X1)
% 1.36/0.97      | ~ v1_xboole_0(X0) ),
% 1.36/0.97      inference(cnf_transformation,[],[f41]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_15,negated_conjecture,
% 1.36/0.97      ( v2_pre_topc(sK0) ),
% 1.36/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_231,plain,
% 1.36/0.97      ( v4_pre_topc(X0,X1)
% 1.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.36/0.97      | ~ l1_pre_topc(X1)
% 1.36/0.97      | ~ v1_xboole_0(X0)
% 1.36/0.97      | sK0 != X1 ),
% 1.36/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_232,plain,
% 1.36/0.97      ( v4_pre_topc(X0,sK0)
% 1.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.36/0.97      | ~ l1_pre_topc(sK0)
% 1.36/0.97      | ~ v1_xboole_0(X0) ),
% 1.36/0.97      inference(unflattening,[status(thm)],[c_231]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_236,plain,
% 1.36/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.36/0.97      | v4_pre_topc(X0,sK0)
% 1.36/0.97      | ~ v1_xboole_0(X0) ),
% 1.36/0.97      inference(global_propositional_subsumption,
% 1.36/0.97                [status(thm)],
% 1.36/0.97                [c_232,c_14]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_237,plain,
% 1.36/0.97      ( v4_pre_topc(X0,sK0)
% 1.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.36/0.97      | ~ v1_xboole_0(X0) ),
% 1.36/0.97      inference(renaming,[status(thm)],[c_236]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_11,plain,
% 1.36/0.97      ( ~ v4_pre_topc(X0,X1)
% 1.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.36/0.97      | ~ l1_pre_topc(X1)
% 1.36/0.97      | k2_pre_topc(X1,X0) = X0 ),
% 1.36/0.97      inference(cnf_transformation,[],[f46]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_272,plain,
% 1.36/0.97      ( ~ v4_pre_topc(X0,X1)
% 1.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.36/0.97      | k2_pre_topc(X1,X0) = X0
% 1.36/0.97      | sK0 != X1 ),
% 1.36/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_273,plain,
% 1.36/0.97      ( ~ v4_pre_topc(X0,sK0)
% 1.36/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.36/0.97      | k2_pre_topc(sK0,X0) = X0 ),
% 1.36/0.97      inference(unflattening,[status(thm)],[c_272]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_318,plain,
% 1.36/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.36/0.97      | ~ v1_xboole_0(X0)
% 1.36/0.97      | k2_pre_topc(sK0,X0) = X0 ),
% 1.36/0.97      inference(resolution,[status(thm)],[c_237,c_273]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_355,plain,
% 1.36/0.97      ( ~ v1_xboole_0(X0)
% 1.36/0.97      | k2_pre_topc(sK0,X0) = X0
% 1.36/0.97      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
% 1.36/0.97      | k1_xboole_0 != X0 ),
% 1.36/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_318]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_356,plain,
% 1.36/0.97      ( ~ v1_xboole_0(k1_xboole_0)
% 1.36/0.97      | k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0
% 1.36/0.97      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 1.36/0.97      inference(unflattening,[status(thm)],[c_355]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_360,plain,
% 1.36/0.97      ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0
% 1.36/0.97      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 1.36/0.97      inference(global_propositional_subsumption,
% 1.36/0.97                [status(thm)],
% 1.36/0.97                [c_356,c_0]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_442,plain,( X0 = X0 ),theory(equality) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_588,plain,
% 1.36/0.97      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.36/0.97      inference(instantiation,[status(thm)],[c_442]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_589,plain,
% 1.36/0.97      ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0
% 1.36/0.97      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 1.36/0.97      inference(instantiation,[status(thm)],[c_360]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_713,plain,
% 1.36/0.97      ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
% 1.36/0.97      inference(global_propositional_subsumption,
% 1.36/0.97                [status(thm)],
% 1.36/0.97                [c_360,c_588,c_589]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_1338,plain,
% 1.36/0.97      ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
% 1.36/0.97      inference(light_normalisation,[status(thm)],[c_1336,c_713]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_1339,plain,
% 1.36/0.97      ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 1.36/0.97      inference(demodulation,[status(thm)],[c_1338,c_2]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_13,negated_conjecture,
% 1.36/0.97      ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
% 1.36/0.97      inference(cnf_transformation,[],[f51]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(c_1014,plain,
% 1.36/0.97      ( k1_tops_1(sK0,u1_struct_0(sK0)) != u1_struct_0(sK0) ),
% 1.36/0.97      inference(demodulation,[status(thm)],[c_1007,c_13]) ).
% 1.36/0.97  
% 1.36/0.97  cnf(contradiction,plain,
% 1.36/0.97      ( $false ),
% 1.36/0.97      inference(minisat,[status(thm)],[c_1339,c_1014]) ).
% 1.36/0.97  
% 1.36/0.97  
% 1.36/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.36/0.97  
% 1.36/0.97  ------                               Statistics
% 1.36/0.97  
% 1.36/0.97  ------ General
% 1.36/0.97  
% 1.36/0.97  abstr_ref_over_cycles:                  0
% 1.36/0.97  abstr_ref_under_cycles:                 0
% 1.36/0.97  gc_basic_clause_elim:                   0
% 1.36/0.97  forced_gc_time:                         0
% 1.36/0.97  parsing_time:                           0.009
% 1.36/0.97  unif_index_cands_time:                  0.
% 1.36/0.97  unif_index_add_time:                    0.
% 1.36/0.97  orderings_time:                         0.
% 1.36/0.97  out_proof_time:                         0.01
% 1.36/0.97  total_time:                             0.079
% 1.36/0.97  num_of_symbols:                         46
% 1.36/0.97  num_of_terms:                           988
% 1.36/0.97  
% 1.36/0.97  ------ Preprocessing
% 1.36/0.97  
% 1.36/0.97  num_of_splits:                          0
% 1.36/0.97  num_of_split_atoms:                     0
% 1.36/0.97  num_of_reused_defs:                     0
% 1.36/0.97  num_eq_ax_congr_red:                    6
% 1.36/0.97  num_of_sem_filtered_clauses:            1
% 1.36/0.97  num_of_subtypes:                        0
% 1.36/0.97  monotx_restored_types:                  0
% 1.36/0.97  sat_num_of_epr_types:                   0
% 1.36/0.97  sat_num_of_non_cyclic_types:            0
% 1.36/0.97  sat_guarded_non_collapsed_types:        0
% 1.36/0.97  num_pure_diseq_elim:                    0
% 1.36/0.97  simp_replaced_by:                       0
% 1.36/0.97  res_preprocessed:                       73
% 1.36/0.97  prep_upred:                             0
% 1.36/0.97  prep_unflattend:                        13
% 1.36/0.97  smt_new_axioms:                         0
% 1.36/0.97  pred_elim_cands:                        1
% 1.36/0.97  pred_elim:                              5
% 1.36/0.97  pred_elim_cl:                           4
% 1.36/0.97  pred_elim_cycles:                       7
% 1.36/0.97  merged_defs:                            0
% 1.36/0.97  merged_defs_ncl:                        0
% 1.36/0.97  bin_hyper_res:                          0
% 1.36/0.97  prep_cycles:                            4
% 1.36/0.97  pred_elim_time:                         0.004
% 1.36/0.97  splitting_time:                         0.
% 1.36/0.97  sem_filter_time:                        0.
% 1.36/0.97  monotx_time:                            0.
% 1.36/0.97  subtype_inf_time:                       0.
% 1.36/0.97  
% 1.36/0.97  ------ Problem properties
% 1.36/0.97  
% 1.36/0.97  clauses:                                12
% 1.36/0.97  conjectures:                            1
% 1.36/0.97  epr:                                    2
% 1.36/0.97  horn:                                   12
% 1.36/0.97  ground:                                 6
% 1.36/0.97  unary:                                  6
% 1.36/0.97  binary:                                 5
% 1.36/0.97  lits:                                   19
% 1.36/0.97  lits_eq:                                14
% 1.36/0.97  fd_pure:                                0
% 1.36/0.97  fd_pseudo:                              0
% 1.36/0.97  fd_cond:                                0
% 1.36/0.97  fd_pseudo_cond:                         1
% 1.36/0.97  ac_symbols:                             0
% 1.36/0.97  
% 1.36/0.97  ------ Propositional Solver
% 1.36/0.97  
% 1.36/0.97  prop_solver_calls:                      28
% 1.36/0.97  prop_fast_solver_calls:                 363
% 1.36/0.97  smt_solver_calls:                       0
% 1.36/0.97  smt_fast_solver_calls:                  0
% 1.36/0.97  prop_num_of_clauses:                    543
% 1.36/0.97  prop_preprocess_simplified:             2041
% 1.36/0.97  prop_fo_subsumed:                       4
% 1.36/0.97  prop_solver_time:                       0.
% 1.36/0.97  smt_solver_time:                        0.
% 1.36/0.97  smt_fast_solver_time:                   0.
% 1.36/0.97  prop_fast_solver_time:                  0.
% 1.36/0.97  prop_unsat_core_time:                   0.
% 1.36/0.97  
% 1.36/0.97  ------ QBF
% 1.36/0.97  
% 1.36/0.97  qbf_q_res:                              0
% 1.36/0.97  qbf_num_tautologies:                    0
% 1.36/0.97  qbf_prep_cycles:                        0
% 1.36/0.97  
% 1.36/0.97  ------ BMC1
% 1.36/0.97  
% 1.36/0.97  bmc1_current_bound:                     -1
% 1.36/0.97  bmc1_last_solved_bound:                 -1
% 1.36/0.97  bmc1_unsat_core_size:                   -1
% 1.36/0.97  bmc1_unsat_core_parents_size:           -1
% 1.36/0.97  bmc1_merge_next_fun:                    0
% 1.36/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.36/0.97  
% 1.36/0.97  ------ Instantiation
% 1.36/0.97  
% 1.36/0.97  inst_num_of_clauses:                    219
% 1.36/0.97  inst_num_in_passive:                    91
% 1.36/0.97  inst_num_in_active:                     117
% 1.36/0.97  inst_num_in_unprocessed:                11
% 1.36/0.97  inst_num_of_loops:                      120
% 1.36/0.97  inst_num_of_learning_restarts:          0
% 1.36/0.97  inst_num_moves_active_passive:          0
% 1.36/0.97  inst_lit_activity:                      0
% 1.36/0.97  inst_lit_activity_moves:                0
% 1.36/0.97  inst_num_tautologies:                   0
% 1.36/0.97  inst_num_prop_implied:                  0
% 1.36/0.97  inst_num_existing_simplified:           0
% 1.36/0.97  inst_num_eq_res_simplified:             0
% 1.36/0.97  inst_num_child_elim:                    0
% 1.36/0.97  inst_num_of_dismatching_blockings:      13
% 1.36/0.97  inst_num_of_non_proper_insts:           186
% 1.36/0.97  inst_num_of_duplicates:                 0
% 1.36/0.97  inst_inst_num_from_inst_to_res:         0
% 1.36/0.97  inst_dismatching_checking_time:         0.
% 1.36/0.97  
% 1.36/0.97  ------ Resolution
% 1.36/0.97  
% 1.36/0.97  res_num_of_clauses:                     0
% 1.36/0.97  res_num_in_passive:                     0
% 1.36/0.97  res_num_in_active:                      0
% 1.36/0.97  res_num_of_loops:                       77
% 1.36/0.97  res_forward_subset_subsumed:            38
% 1.36/0.97  res_backward_subset_subsumed:           0
% 1.36/0.97  res_forward_subsumed:                   0
% 1.36/0.97  res_backward_subsumed:                  0
% 1.36/0.97  res_forward_subsumption_resolution:     0
% 1.36/0.97  res_backward_subsumption_resolution:    0
% 1.36/0.97  res_clause_to_clause_subsumption:       29
% 1.36/0.97  res_orphan_elimination:                 0
% 1.36/0.97  res_tautology_del:                      24
% 1.36/0.97  res_num_eq_res_simplified:              0
% 1.36/0.97  res_num_sel_changes:                    0
% 1.36/0.97  res_moves_from_active_to_pass:          0
% 1.36/0.97  
% 1.36/0.97  ------ Superposition
% 1.36/0.97  
% 1.36/0.97  sup_time_total:                         0.
% 1.36/0.97  sup_time_generating:                    0.
% 1.36/0.97  sup_time_sim_full:                      0.
% 1.36/0.97  sup_time_sim_immed:                     0.
% 1.36/0.97  
% 1.36/0.97  sup_num_of_clauses:                     13
% 1.36/0.97  sup_num_in_active:                      10
% 1.36/0.97  sup_num_in_passive:                     3
% 1.36/0.97  sup_num_of_loops:                       22
% 1.36/0.97  sup_fw_superposition:                   4
% 1.36/0.97  sup_bw_superposition:                   0
% 1.36/0.97  sup_immediate_simplified:               5
% 1.36/0.97  sup_given_eliminated:                   1
% 1.36/0.97  comparisons_done:                       0
% 1.36/0.97  comparisons_avoided:                    0
% 1.36/0.97  
% 1.36/0.97  ------ Simplifications
% 1.36/0.97  
% 1.36/0.97  
% 1.36/0.97  sim_fw_subset_subsumed:                 0
% 1.36/0.97  sim_bw_subset_subsumed:                 4
% 1.36/0.97  sim_fw_subsumed:                        1
% 1.36/0.97  sim_bw_subsumed:                        0
% 1.36/0.97  sim_fw_subsumption_res:                 0
% 1.36/0.97  sim_bw_subsumption_res:                 0
% 1.36/0.97  sim_tautology_del:                      0
% 1.36/0.97  sim_eq_tautology_del:                   2
% 1.36/0.97  sim_eq_res_simp:                        0
% 1.36/0.97  sim_fw_demodulated:                     3
% 1.36/0.97  sim_bw_demodulated:                     10
% 1.36/0.97  sim_light_normalised:                   2
% 1.36/0.97  sim_joinable_taut:                      0
% 1.36/0.97  sim_joinable_simp:                      0
% 1.36/0.97  sim_ac_normalised:                      0
% 1.36/0.97  sim_smt_subsumption:                    0
% 1.36/0.97  
%------------------------------------------------------------------------------

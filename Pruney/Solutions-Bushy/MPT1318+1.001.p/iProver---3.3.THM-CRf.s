%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1318+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:27 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 269 expanded)
%              Number of clauses        :   59 ( 107 expanded)
%              Number of leaves         :   13 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  237 ( 784 expanded)
%              Number of equality atoms :   82 ( 125 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,sK2))))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26,f25,f24])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1021,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1302,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1026,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | m1_pre_topc(k1_pre_topc(X0_43,X0_44),X0_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1297,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | m1_pre_topc(k1_pre_topc(X0_43,X0_44),X0_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_1804,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_1297])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1061,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | m1_pre_topc(k1_pre_topc(X0_43,X0_44),X0_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_1063,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_2138,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1804,c_15,c_17,c_1063])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1024,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1299,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | l1_pre_topc(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_2143,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2138,c_1299])).

cnf(c_2485,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2143,c_15])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_180,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_3])).

cnf(c_1016,plain,
    ( ~ l1_pre_topc(X0_43)
    | u1_struct_0(X0_43) = k2_struct_0(X0_43) ),
    inference(subtyping,[status(esa)],[c_180])).

cnf(c_1307,plain,
    ( u1_struct_0(X0_43) = k2_struct_0(X0_43)
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_2490,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK2)) = k2_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_2485,c_1307])).

cnf(c_1019,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1304,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_1509,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1304,c_1307])).

cnf(c_1835,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1509,c_1302])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_89,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_5,c_4])).

cnf(c_90,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_89])).

cnf(c_1018,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_pre_topc(X0_43)
    | k2_struct_0(k1_pre_topc(X0_43,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_90])).

cnf(c_1305,plain,
    ( k2_struct_0(k1_pre_topc(X0_43,X0_44)) = X0_44
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_2151,plain,
    ( k2_struct_0(k1_pre_topc(sK0,X0_44)) = X0_44
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1305])).

cnf(c_2556,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k2_struct_0(k1_pre_topc(sK0,X0_44)) = X0_44 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2151,c_15])).

cnf(c_2557,plain,
    ( k2_struct_0(k1_pre_topc(sK0,X0_44)) = X0_44
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2556])).

cnf(c_2567,plain,
    ( k2_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1835,c_2557])).

cnf(c_3328,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2490,c_2567])).

cnf(c_11,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1022,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1301,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_1833,plain,
    ( m1_subset_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1509,c_1301])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k9_subset_1(X1_44,X2_44,X0_44) = k3_xboole_0(X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1300,plain,
    ( k9_subset_1(X0_44,X1_44,X2_44) = k3_xboole_0(X1_44,X2_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_1932,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0_44,sK2) = k3_xboole_0(X0_44,sK2) ),
    inference(superposition,[status(thm)],[c_1835,c_1300])).

cnf(c_2451,plain,
    ( m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1833,c_1932])).

cnf(c_3330,plain,
    ( m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3328,c_2451])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1028,plain,
    ( k3_xboole_0(X0_44,X1_44) = k3_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_9,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_169,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k3_xboole_0(X2,X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_170,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_1017,plain,
    ( m1_subset_1(k3_xboole_0(X0_44,X1_44),k1_zfmisc_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_170])).

cnf(c_1306,plain,
    ( m1_subset_1(k3_xboole_0(X0_44,X1_44),k1_zfmisc_1(X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_1446,plain,
    ( m1_subset_1(k3_xboole_0(X0_44,X1_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1306])).

cnf(c_3673,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3330,c_1446])).


%------------------------------------------------------------------------------

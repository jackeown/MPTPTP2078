%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1265+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:16 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 255 expanded)
%              Number of clauses        :   49 (  70 expanded)
%              Number of leaves         :    9 (  78 expanded)
%              Depth                    :   19
%              Number of atoms          :  255 (1591 expanded)
%              Number of equality atoms :   74 ( 106 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v3_pre_topc(X2,X0)
          & v1_tops_1(X2,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK5),X0)
        & v3_pre_topc(sK5,X0)
        & v1_tops_1(sK5,X0)
        & v1_tops_1(X1,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),sK4,X2),X0)
            & v3_pre_topc(X2,X0)
            & v1_tops_1(X2,X0)
            & v1_tops_1(sK4,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK3),X1,X2),sK3)
              & v3_pre_topc(X2,sK3)
              & v1_tops_1(X2,sK3)
              & v1_tops_1(X1,sK3)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK3),sK4,sK5),sK3)
    & v3_pre_topc(sK5,sK3)
    & v1_tops_1(sK5,sK3)
    & v1_tops_1(sK4,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f46,f45,f44])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f67,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    v1_tops_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    v1_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK3),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1469,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1475,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3072,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_1469,c_1475])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,negated_conjecture,
    ( v3_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0)
    | sK5 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(X0,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK5,X0)) = k2_pre_topc(sK3,sK5) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(X0,sK3)
    | k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK5,X0)) = k2_pre_topc(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_25,c_24,c_22])).

cnf(c_1466,plain,
    ( k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK5,X0)) = k2_pre_topc(sK3,sK5)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_tops_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1470,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X0,X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(X0,sK3)
    | k2_pre_topc(sK3,X0) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_1457,plain,
    ( k2_pre_topc(sK3,X0) = k2_struct_0(sK3)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_tops_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_2494,plain,
    ( k2_pre_topc(sK3,sK5) = k2_struct_0(sK3)
    | v1_tops_1(sK5,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1457])).

cnf(c_20,negated_conjecture,
    ( v1_tops_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = k2_struct_0(sK3)
    | sK5 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_427])).

cnf(c_542,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK5) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_2653,plain,
    ( k2_pre_topc(sK3,sK5) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2494,c_22,c_542])).

cnf(c_2759,plain,
    ( k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK5,X0)) = k2_struct_0(sK3)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_tops_1(X0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1466,c_2653])).

cnf(c_2767,plain,
    ( k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK5,sK4)) = k2_struct_0(sK3)
    | v1_tops_1(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_2759])).

cnf(c_21,negated_conjecture,
    ( v1_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,plain,
    ( v1_tops_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2879,plain,
    ( k2_pre_topc(sK3,k9_subset_1(u1_struct_0(sK3),sK5,sK4)) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2767,c_30])).

cnf(c_3479,plain,
    ( k2_pre_topc(sK3,k3_xboole_0(sK5,sK4)) = k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_3072,c_2879])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_24])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_1(X0,sK3)
    | k2_pre_topc(sK3,X0) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_1456,plain,
    ( k2_pre_topc(sK3,X0) != k2_struct_0(sK3)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_tops_1(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_3675,plain,
    ( m1_subset_1(k3_xboole_0(sK5,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_tops_1(k3_xboole_0(sK5,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3479,c_1456])).

cnf(c_3071,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_1470,c_1475])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1478,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3393,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3071,c_1478])).

cnf(c_29,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4175,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3393,c_29])).

cnf(c_4182,plain,
    ( m1_subset_1(k3_xboole_0(sK5,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_4175])).

cnf(c_5793,plain,
    ( v1_tops_1(k3_xboole_0(sK5,sK4),sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3675,c_4182])).

cnf(c_5795,plain,
    ( v1_tops_1(k3_xboole_0(sK4,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_5793])).

cnf(c_18,negated_conjecture,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK3),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1473,plain,
    ( v1_tops_1(k9_subset_1(u1_struct_0(sK3),sK4,sK5),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3386,plain,
    ( v1_tops_1(k3_xboole_0(sK4,sK5),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3071,c_1473])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5795,c_3386])).


%------------------------------------------------------------------------------

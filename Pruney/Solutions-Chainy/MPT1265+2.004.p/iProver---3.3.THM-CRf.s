%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:56 EST 2020

% Result     : Theorem 14.87s
% Output     : CNFRefutation 14.87s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 545 expanded)
%              Number of clauses        :   85 ( 187 expanded)
%              Number of leaves         :   14 ( 146 expanded)
%              Depth                    :   23
%              Number of atoms          :  346 (2608 expanded)
%              Number of equality atoms :  112 ( 246 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v3_pre_topc(X2,X0)
          & v1_tops_1(X2,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v3_pre_topc(sK2,X0)
        & v1_tops_1(sK2,X0)
        & v1_tops_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v3_pre_topc(X2,X0)
            & v1_tops_1(X2,X0)
            & v1_tops_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f29,f28,f27])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1336,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_271,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_310,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_271,c_19])).

cnf(c_311,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1342,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1336,c_311])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1338,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1630,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_1338])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1341,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1929,plain,
    ( k2_xboole_0(sK1,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1630,c_1341])).

cnf(c_2,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1340,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2120,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1929,c_1340])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1339,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1337,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1343,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1337,c_311])).

cnf(c_1631,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_1338])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_156,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_191,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_156])).

cnf(c_1334,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_25780,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_1631,c_1334])).

cnf(c_13,negated_conjecture,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_330,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_331,plain,
    ( v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_331])).

cnf(c_399,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1331,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1349,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
    | m1_subset_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1331,c_311])).

cnf(c_26499,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k2_struct_0(sK0)
    | m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25780,c_1349])).

cnf(c_25779,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_1630,c_1334])).

cnf(c_16,negated_conjecture,
    ( v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v1_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_285,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X0)) = k2_pre_topc(X1,X2)
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_286,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(X0,sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_20,c_19,c_17])).

cnf(c_291,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_291])).

cnf(c_433,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_435,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_18])).

cnf(c_15,negated_conjecture,
    ( v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_315,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_316,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_316])).

cnf(c_409,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_411,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_17])).

cnf(c_1346,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_435,c_311,c_411])).

cnf(c_26392,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_25779,c_1346])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1333,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1348,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1333,c_311])).

cnf(c_2038,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1348])).

cnf(c_2322,plain,
    ( k2_xboole_0(X0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_1341])).

cnf(c_2329,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,X0),k2_pre_topc(sK0,k3_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2120,c_2322])).

cnf(c_2607,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X0),X1),k2_pre_topc(sK0,k3_xboole_0(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2329,c_1340])).

cnf(c_3273,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),X1),k2_pre_topc(sK0,k3_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2607,c_1341])).

cnf(c_15921,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),X1),k2_pre_topc(sK0,k3_xboole_0(X0,sK1))) = k2_pre_topc(sK0,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_3273])).

cnf(c_16099,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),k2_pre_topc(sK0,k3_xboole_0(X1,sK1))) = k2_pre_topc(sK0,k3_xboole_0(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_15921])).

cnf(c_26486,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,sK1)),k2_struct_0(sK0)) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_26392,c_16099])).

cnf(c_1966,plain,
    ( k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1631,c_1341])).

cnf(c_2128,plain,
    ( r1_tarski(k3_xboole_0(sK2,X0),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1966,c_1340])).

cnf(c_2527,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,X0),k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_2128,c_1341])).

cnf(c_1703,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1340])).

cnf(c_2860,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2527,c_1703])).

cnf(c_5156,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_2860,c_1341])).

cnf(c_26491,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_26486,c_5156])).

cnf(c_26507,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26499,c_26491])).

cnf(c_26508,plain,
    ( m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_26507])).

cnf(c_28174,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_26508])).

cnf(c_48616,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2120,c_28174])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:43:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 14.87/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.87/2.49  
% 14.87/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.87/2.49  
% 14.87/2.49  ------  iProver source info
% 14.87/2.49  
% 14.87/2.49  git: date: 2020-06-30 10:37:57 +0100
% 14.87/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.87/2.49  git: non_committed_changes: false
% 14.87/2.49  git: last_make_outside_of_git: false
% 14.87/2.49  
% 14.87/2.49  ------ 
% 14.87/2.49  
% 14.87/2.49  ------ Input Options
% 14.87/2.49  
% 14.87/2.49  --out_options                           all
% 14.87/2.49  --tptp_safe_out                         true
% 14.87/2.49  --problem_path                          ""
% 14.87/2.49  --include_path                          ""
% 14.87/2.49  --clausifier                            res/vclausify_rel
% 14.87/2.49  --clausifier_options                    ""
% 14.87/2.49  --stdin                                 false
% 14.87/2.49  --stats_out                             all
% 14.87/2.49  
% 14.87/2.49  ------ General Options
% 14.87/2.49  
% 14.87/2.49  --fof                                   false
% 14.87/2.49  --time_out_real                         305.
% 14.87/2.49  --time_out_virtual                      -1.
% 14.87/2.49  --symbol_type_check                     false
% 14.87/2.49  --clausify_out                          false
% 14.87/2.49  --sig_cnt_out                           false
% 14.87/2.49  --trig_cnt_out                          false
% 14.87/2.49  --trig_cnt_out_tolerance                1.
% 14.87/2.49  --trig_cnt_out_sk_spl                   false
% 14.87/2.49  --abstr_cl_out                          false
% 14.87/2.49  
% 14.87/2.49  ------ Global Options
% 14.87/2.49  
% 14.87/2.49  --schedule                              default
% 14.87/2.49  --add_important_lit                     false
% 14.87/2.49  --prop_solver_per_cl                    1000
% 14.87/2.49  --min_unsat_core                        false
% 14.87/2.49  --soft_assumptions                      false
% 14.87/2.49  --soft_lemma_size                       3
% 14.87/2.49  --prop_impl_unit_size                   0
% 14.87/2.49  --prop_impl_unit                        []
% 14.87/2.49  --share_sel_clauses                     true
% 14.87/2.49  --reset_solvers                         false
% 14.87/2.49  --bc_imp_inh                            [conj_cone]
% 14.87/2.49  --conj_cone_tolerance                   3.
% 14.87/2.49  --extra_neg_conj                        none
% 14.87/2.49  --large_theory_mode                     true
% 14.87/2.49  --prolific_symb_bound                   200
% 14.87/2.49  --lt_threshold                          2000
% 14.87/2.49  --clause_weak_htbl                      true
% 14.87/2.49  --gc_record_bc_elim                     false
% 14.87/2.49  
% 14.87/2.49  ------ Preprocessing Options
% 14.87/2.49  
% 14.87/2.49  --preprocessing_flag                    true
% 14.87/2.49  --time_out_prep_mult                    0.1
% 14.87/2.49  --splitting_mode                        input
% 14.87/2.49  --splitting_grd                         true
% 14.87/2.49  --splitting_cvd                         false
% 14.87/2.49  --splitting_cvd_svl                     false
% 14.87/2.49  --splitting_nvd                         32
% 14.87/2.49  --sub_typing                            true
% 14.87/2.49  --prep_gs_sim                           true
% 14.87/2.49  --prep_unflatten                        true
% 14.87/2.49  --prep_res_sim                          true
% 14.87/2.49  --prep_upred                            true
% 14.87/2.49  --prep_sem_filter                       exhaustive
% 14.87/2.49  --prep_sem_filter_out                   false
% 14.87/2.49  --pred_elim                             true
% 14.87/2.49  --res_sim_input                         true
% 14.87/2.49  --eq_ax_congr_red                       true
% 14.87/2.49  --pure_diseq_elim                       true
% 14.87/2.49  --brand_transform                       false
% 14.87/2.49  --non_eq_to_eq                          false
% 14.87/2.49  --prep_def_merge                        true
% 14.87/2.49  --prep_def_merge_prop_impl              false
% 14.87/2.49  --prep_def_merge_mbd                    true
% 14.87/2.49  --prep_def_merge_tr_red                 false
% 14.87/2.49  --prep_def_merge_tr_cl                  false
% 14.87/2.49  --smt_preprocessing                     true
% 14.87/2.49  --smt_ac_axioms                         fast
% 14.87/2.49  --preprocessed_out                      false
% 14.87/2.49  --preprocessed_stats                    false
% 14.87/2.49  
% 14.87/2.49  ------ Abstraction refinement Options
% 14.87/2.49  
% 14.87/2.49  --abstr_ref                             []
% 14.87/2.49  --abstr_ref_prep                        false
% 14.87/2.49  --abstr_ref_until_sat                   false
% 14.87/2.49  --abstr_ref_sig_restrict                funpre
% 14.87/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 14.87/2.49  --abstr_ref_under                       []
% 14.87/2.49  
% 14.87/2.49  ------ SAT Options
% 14.87/2.49  
% 14.87/2.49  --sat_mode                              false
% 14.87/2.49  --sat_fm_restart_options                ""
% 14.87/2.49  --sat_gr_def                            false
% 14.87/2.49  --sat_epr_types                         true
% 14.87/2.49  --sat_non_cyclic_types                  false
% 14.87/2.49  --sat_finite_models                     false
% 14.87/2.49  --sat_fm_lemmas                         false
% 14.87/2.49  --sat_fm_prep                           false
% 14.87/2.49  --sat_fm_uc_incr                        true
% 14.87/2.49  --sat_out_model                         small
% 14.87/2.49  --sat_out_clauses                       false
% 14.87/2.49  
% 14.87/2.49  ------ QBF Options
% 14.87/2.49  
% 14.87/2.49  --qbf_mode                              false
% 14.87/2.49  --qbf_elim_univ                         false
% 14.87/2.49  --qbf_dom_inst                          none
% 14.87/2.49  --qbf_dom_pre_inst                      false
% 14.87/2.49  --qbf_sk_in                             false
% 14.87/2.49  --qbf_pred_elim                         true
% 14.87/2.49  --qbf_split                             512
% 14.87/2.49  
% 14.87/2.49  ------ BMC1 Options
% 14.87/2.49  
% 14.87/2.49  --bmc1_incremental                      false
% 14.87/2.49  --bmc1_axioms                           reachable_all
% 14.87/2.49  --bmc1_min_bound                        0
% 14.87/2.49  --bmc1_max_bound                        -1
% 14.87/2.49  --bmc1_max_bound_default                -1
% 14.87/2.49  --bmc1_symbol_reachability              true
% 14.87/2.49  --bmc1_property_lemmas                  false
% 14.87/2.49  --bmc1_k_induction                      false
% 14.87/2.49  --bmc1_non_equiv_states                 false
% 14.87/2.49  --bmc1_deadlock                         false
% 14.87/2.49  --bmc1_ucm                              false
% 14.87/2.49  --bmc1_add_unsat_core                   none
% 14.87/2.49  --bmc1_unsat_core_children              false
% 14.87/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 14.87/2.49  --bmc1_out_stat                         full
% 14.87/2.49  --bmc1_ground_init                      false
% 14.87/2.49  --bmc1_pre_inst_next_state              false
% 14.87/2.49  --bmc1_pre_inst_state                   false
% 14.87/2.49  --bmc1_pre_inst_reach_state             false
% 14.87/2.49  --bmc1_out_unsat_core                   false
% 14.87/2.49  --bmc1_aig_witness_out                  false
% 14.87/2.49  --bmc1_verbose                          false
% 14.87/2.49  --bmc1_dump_clauses_tptp                false
% 14.87/2.49  --bmc1_dump_unsat_core_tptp             false
% 14.87/2.49  --bmc1_dump_file                        -
% 14.87/2.49  --bmc1_ucm_expand_uc_limit              128
% 14.87/2.49  --bmc1_ucm_n_expand_iterations          6
% 14.87/2.49  --bmc1_ucm_extend_mode                  1
% 14.87/2.49  --bmc1_ucm_init_mode                    2
% 14.87/2.49  --bmc1_ucm_cone_mode                    none
% 14.87/2.49  --bmc1_ucm_reduced_relation_type        0
% 14.87/2.49  --bmc1_ucm_relax_model                  4
% 14.87/2.49  --bmc1_ucm_full_tr_after_sat            true
% 14.87/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 14.87/2.49  --bmc1_ucm_layered_model                none
% 14.87/2.49  --bmc1_ucm_max_lemma_size               10
% 14.87/2.49  
% 14.87/2.49  ------ AIG Options
% 14.87/2.49  
% 14.87/2.49  --aig_mode                              false
% 14.87/2.49  
% 14.87/2.49  ------ Instantiation Options
% 14.87/2.49  
% 14.87/2.49  --instantiation_flag                    true
% 14.87/2.49  --inst_sos_flag                         true
% 14.87/2.49  --inst_sos_phase                        true
% 14.87/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.87/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.87/2.49  --inst_lit_sel_side                     num_symb
% 14.87/2.49  --inst_solver_per_active                1400
% 14.87/2.49  --inst_solver_calls_frac                1.
% 14.87/2.49  --inst_passive_queue_type               priority_queues
% 14.87/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.87/2.49  --inst_passive_queues_freq              [25;2]
% 14.87/2.49  --inst_dismatching                      true
% 14.87/2.49  --inst_eager_unprocessed_to_passive     true
% 14.87/2.49  --inst_prop_sim_given                   true
% 14.87/2.49  --inst_prop_sim_new                     false
% 14.87/2.49  --inst_subs_new                         false
% 14.87/2.49  --inst_eq_res_simp                      false
% 14.87/2.49  --inst_subs_given                       false
% 14.87/2.49  --inst_orphan_elimination               true
% 14.87/2.49  --inst_learning_loop_flag               true
% 14.87/2.49  --inst_learning_start                   3000
% 14.87/2.49  --inst_learning_factor                  2
% 14.87/2.49  --inst_start_prop_sim_after_learn       3
% 14.87/2.49  --inst_sel_renew                        solver
% 14.87/2.49  --inst_lit_activity_flag                true
% 14.87/2.49  --inst_restr_to_given                   false
% 14.87/2.49  --inst_activity_threshold               500
% 14.87/2.49  --inst_out_proof                        true
% 14.87/2.49  
% 14.87/2.49  ------ Resolution Options
% 14.87/2.49  
% 14.87/2.49  --resolution_flag                       true
% 14.87/2.49  --res_lit_sel                           adaptive
% 14.87/2.49  --res_lit_sel_side                      none
% 14.87/2.49  --res_ordering                          kbo
% 14.87/2.49  --res_to_prop_solver                    active
% 14.87/2.49  --res_prop_simpl_new                    false
% 14.87/2.49  --res_prop_simpl_given                  true
% 14.87/2.49  --res_passive_queue_type                priority_queues
% 14.87/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.87/2.49  --res_passive_queues_freq               [15;5]
% 14.87/2.49  --res_forward_subs                      full
% 14.87/2.49  --res_backward_subs                     full
% 14.87/2.49  --res_forward_subs_resolution           true
% 14.87/2.49  --res_backward_subs_resolution          true
% 14.87/2.49  --res_orphan_elimination                true
% 14.87/2.49  --res_time_limit                        2.
% 14.87/2.49  --res_out_proof                         true
% 14.87/2.49  
% 14.87/2.49  ------ Superposition Options
% 14.87/2.49  
% 14.87/2.49  --superposition_flag                    true
% 14.87/2.49  --sup_passive_queue_type                priority_queues
% 14.87/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.87/2.49  --sup_passive_queues_freq               [8;1;4]
% 14.87/2.49  --demod_completeness_check              fast
% 14.87/2.49  --demod_use_ground                      true
% 14.87/2.49  --sup_to_prop_solver                    passive
% 14.87/2.49  --sup_prop_simpl_new                    true
% 14.87/2.49  --sup_prop_simpl_given                  true
% 14.87/2.49  --sup_fun_splitting                     true
% 14.87/2.49  --sup_smt_interval                      50000
% 14.87/2.49  
% 14.87/2.49  ------ Superposition Simplification Setup
% 14.87/2.49  
% 14.87/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 14.87/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 14.87/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 14.87/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 14.87/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 14.87/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 14.87/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 14.87/2.49  --sup_immed_triv                        [TrivRules]
% 14.87/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.87/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.87/2.49  --sup_immed_bw_main                     []
% 14.87/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 14.87/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 14.87/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.87/2.49  --sup_input_bw                          []
% 14.87/2.49  
% 14.87/2.49  ------ Combination Options
% 14.87/2.49  
% 14.87/2.49  --comb_res_mult                         3
% 14.87/2.49  --comb_sup_mult                         2
% 14.87/2.49  --comb_inst_mult                        10
% 14.87/2.49  
% 14.87/2.49  ------ Debug Options
% 14.87/2.49  
% 14.87/2.49  --dbg_backtrace                         false
% 14.87/2.49  --dbg_dump_prop_clauses                 false
% 14.87/2.49  --dbg_dump_prop_clauses_file            -
% 14.87/2.49  --dbg_out_stat                          false
% 14.87/2.49  ------ Parsing...
% 14.87/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.87/2.49  
% 14.87/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 14.87/2.49  
% 14.87/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.87/2.49  
% 14.87/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.87/2.49  ------ Proving...
% 14.87/2.49  ------ Problem Properties 
% 14.87/2.49  
% 14.87/2.49  
% 14.87/2.49  clauses                                 19
% 14.87/2.49  conjectures                             2
% 14.87/2.49  EPR                                     0
% 14.87/2.49  Horn                                    19
% 14.87/2.49  unary                                   11
% 14.87/2.49  binary                                  7
% 14.87/2.49  lits                                    28
% 14.87/2.49  lits eq                                 14
% 14.87/2.49  fd_pure                                 0
% 14.87/2.49  fd_pseudo                               0
% 14.87/2.49  fd_cond                                 0
% 14.87/2.49  fd_pseudo_cond                          0
% 14.87/2.49  AC symbols                              0
% 14.87/2.49  
% 14.87/2.49  ------ Schedule dynamic 5 is on 
% 14.87/2.49  
% 14.87/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 14.87/2.49  
% 14.87/2.49  
% 14.87/2.49  ------ 
% 14.87/2.49  Current options:
% 14.87/2.49  ------ 
% 14.87/2.49  
% 14.87/2.49  ------ Input Options
% 14.87/2.49  
% 14.87/2.49  --out_options                           all
% 14.87/2.49  --tptp_safe_out                         true
% 14.87/2.49  --problem_path                          ""
% 14.87/2.49  --include_path                          ""
% 14.87/2.49  --clausifier                            res/vclausify_rel
% 14.87/2.49  --clausifier_options                    ""
% 14.87/2.49  --stdin                                 false
% 14.87/2.49  --stats_out                             all
% 14.87/2.49  
% 14.87/2.49  ------ General Options
% 14.87/2.49  
% 14.87/2.49  --fof                                   false
% 14.87/2.49  --time_out_real                         305.
% 14.87/2.49  --time_out_virtual                      -1.
% 14.87/2.49  --symbol_type_check                     false
% 14.87/2.49  --clausify_out                          false
% 14.87/2.49  --sig_cnt_out                           false
% 14.87/2.49  --trig_cnt_out                          false
% 14.87/2.49  --trig_cnt_out_tolerance                1.
% 14.87/2.49  --trig_cnt_out_sk_spl                   false
% 14.87/2.49  --abstr_cl_out                          false
% 14.87/2.49  
% 14.87/2.49  ------ Global Options
% 14.87/2.49  
% 14.87/2.49  --schedule                              default
% 14.87/2.49  --add_important_lit                     false
% 14.87/2.49  --prop_solver_per_cl                    1000
% 14.87/2.49  --min_unsat_core                        false
% 14.87/2.49  --soft_assumptions                      false
% 14.87/2.49  --soft_lemma_size                       3
% 14.87/2.49  --prop_impl_unit_size                   0
% 14.87/2.49  --prop_impl_unit                        []
% 14.87/2.49  --share_sel_clauses                     true
% 14.87/2.49  --reset_solvers                         false
% 14.87/2.49  --bc_imp_inh                            [conj_cone]
% 14.87/2.49  --conj_cone_tolerance                   3.
% 14.87/2.49  --extra_neg_conj                        none
% 14.87/2.49  --large_theory_mode                     true
% 14.87/2.49  --prolific_symb_bound                   200
% 14.87/2.49  --lt_threshold                          2000
% 14.87/2.49  --clause_weak_htbl                      true
% 14.87/2.49  --gc_record_bc_elim                     false
% 14.87/2.49  
% 14.87/2.49  ------ Preprocessing Options
% 14.87/2.49  
% 14.87/2.49  --preprocessing_flag                    true
% 14.87/2.49  --time_out_prep_mult                    0.1
% 14.87/2.49  --splitting_mode                        input
% 14.87/2.49  --splitting_grd                         true
% 14.87/2.49  --splitting_cvd                         false
% 14.87/2.49  --splitting_cvd_svl                     false
% 14.87/2.49  --splitting_nvd                         32
% 14.87/2.49  --sub_typing                            true
% 14.87/2.49  --prep_gs_sim                           true
% 14.87/2.49  --prep_unflatten                        true
% 14.87/2.49  --prep_res_sim                          true
% 14.87/2.49  --prep_upred                            true
% 14.87/2.49  --prep_sem_filter                       exhaustive
% 14.87/2.49  --prep_sem_filter_out                   false
% 14.87/2.49  --pred_elim                             true
% 14.87/2.49  --res_sim_input                         true
% 14.87/2.49  --eq_ax_congr_red                       true
% 14.87/2.49  --pure_diseq_elim                       true
% 14.87/2.49  --brand_transform                       false
% 14.87/2.49  --non_eq_to_eq                          false
% 14.87/2.49  --prep_def_merge                        true
% 14.87/2.49  --prep_def_merge_prop_impl              false
% 14.87/2.49  --prep_def_merge_mbd                    true
% 14.87/2.49  --prep_def_merge_tr_red                 false
% 14.87/2.49  --prep_def_merge_tr_cl                  false
% 14.87/2.49  --smt_preprocessing                     true
% 14.87/2.49  --smt_ac_axioms                         fast
% 14.87/2.49  --preprocessed_out                      false
% 14.87/2.49  --preprocessed_stats                    false
% 14.87/2.49  
% 14.87/2.49  ------ Abstraction refinement Options
% 14.87/2.49  
% 14.87/2.49  --abstr_ref                             []
% 14.87/2.49  --abstr_ref_prep                        false
% 14.87/2.49  --abstr_ref_until_sat                   false
% 14.87/2.49  --abstr_ref_sig_restrict                funpre
% 14.87/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 14.87/2.49  --abstr_ref_under                       []
% 14.87/2.49  
% 14.87/2.49  ------ SAT Options
% 14.87/2.49  
% 14.87/2.49  --sat_mode                              false
% 14.87/2.49  --sat_fm_restart_options                ""
% 14.87/2.49  --sat_gr_def                            false
% 14.87/2.49  --sat_epr_types                         true
% 14.87/2.49  --sat_non_cyclic_types                  false
% 14.87/2.49  --sat_finite_models                     false
% 14.87/2.49  --sat_fm_lemmas                         false
% 14.87/2.49  --sat_fm_prep                           false
% 14.87/2.49  --sat_fm_uc_incr                        true
% 14.87/2.49  --sat_out_model                         small
% 14.87/2.49  --sat_out_clauses                       false
% 14.87/2.49  
% 14.87/2.49  ------ QBF Options
% 14.87/2.49  
% 14.87/2.49  --qbf_mode                              false
% 14.87/2.49  --qbf_elim_univ                         false
% 14.87/2.49  --qbf_dom_inst                          none
% 14.87/2.49  --qbf_dom_pre_inst                      false
% 14.87/2.49  --qbf_sk_in                             false
% 14.87/2.49  --qbf_pred_elim                         true
% 14.87/2.49  --qbf_split                             512
% 14.87/2.49  
% 14.87/2.49  ------ BMC1 Options
% 14.87/2.49  
% 14.87/2.49  --bmc1_incremental                      false
% 14.87/2.49  --bmc1_axioms                           reachable_all
% 14.87/2.49  --bmc1_min_bound                        0
% 14.87/2.49  --bmc1_max_bound                        -1
% 14.87/2.49  --bmc1_max_bound_default                -1
% 14.87/2.49  --bmc1_symbol_reachability              true
% 14.87/2.49  --bmc1_property_lemmas                  false
% 14.87/2.49  --bmc1_k_induction                      false
% 14.87/2.49  --bmc1_non_equiv_states                 false
% 14.87/2.49  --bmc1_deadlock                         false
% 14.87/2.49  --bmc1_ucm                              false
% 14.87/2.49  --bmc1_add_unsat_core                   none
% 14.87/2.49  --bmc1_unsat_core_children              false
% 14.87/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 14.87/2.49  --bmc1_out_stat                         full
% 14.87/2.49  --bmc1_ground_init                      false
% 14.87/2.49  --bmc1_pre_inst_next_state              false
% 14.87/2.49  --bmc1_pre_inst_state                   false
% 14.87/2.49  --bmc1_pre_inst_reach_state             false
% 14.87/2.49  --bmc1_out_unsat_core                   false
% 14.87/2.49  --bmc1_aig_witness_out                  false
% 14.87/2.49  --bmc1_verbose                          false
% 14.87/2.49  --bmc1_dump_clauses_tptp                false
% 14.87/2.49  --bmc1_dump_unsat_core_tptp             false
% 14.87/2.49  --bmc1_dump_file                        -
% 14.87/2.49  --bmc1_ucm_expand_uc_limit              128
% 14.87/2.49  --bmc1_ucm_n_expand_iterations          6
% 14.87/2.49  --bmc1_ucm_extend_mode                  1
% 14.87/2.49  --bmc1_ucm_init_mode                    2
% 14.87/2.49  --bmc1_ucm_cone_mode                    none
% 14.87/2.49  --bmc1_ucm_reduced_relation_type        0
% 14.87/2.49  --bmc1_ucm_relax_model                  4
% 14.87/2.49  --bmc1_ucm_full_tr_after_sat            true
% 14.87/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 14.87/2.49  --bmc1_ucm_layered_model                none
% 14.87/2.49  --bmc1_ucm_max_lemma_size               10
% 14.87/2.49  
% 14.87/2.49  ------ AIG Options
% 14.87/2.49  
% 14.87/2.49  --aig_mode                              false
% 14.87/2.49  
% 14.87/2.49  ------ Instantiation Options
% 14.87/2.49  
% 14.87/2.49  --instantiation_flag                    true
% 14.87/2.49  --inst_sos_flag                         true
% 14.87/2.49  --inst_sos_phase                        true
% 14.87/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.87/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.87/2.49  --inst_lit_sel_side                     none
% 14.87/2.49  --inst_solver_per_active                1400
% 14.87/2.49  --inst_solver_calls_frac                1.
% 14.87/2.49  --inst_passive_queue_type               priority_queues
% 14.87/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.87/2.49  --inst_passive_queues_freq              [25;2]
% 14.87/2.49  --inst_dismatching                      true
% 14.87/2.49  --inst_eager_unprocessed_to_passive     true
% 14.87/2.49  --inst_prop_sim_given                   true
% 14.87/2.49  --inst_prop_sim_new                     false
% 14.87/2.49  --inst_subs_new                         false
% 14.87/2.49  --inst_eq_res_simp                      false
% 14.87/2.49  --inst_subs_given                       false
% 14.87/2.49  --inst_orphan_elimination               true
% 14.87/2.49  --inst_learning_loop_flag               true
% 14.87/2.49  --inst_learning_start                   3000
% 14.87/2.49  --inst_learning_factor                  2
% 14.87/2.49  --inst_start_prop_sim_after_learn       3
% 14.87/2.49  --inst_sel_renew                        solver
% 14.87/2.49  --inst_lit_activity_flag                true
% 14.87/2.49  --inst_restr_to_given                   false
% 14.87/2.49  --inst_activity_threshold               500
% 14.87/2.49  --inst_out_proof                        true
% 14.87/2.49  
% 14.87/2.49  ------ Resolution Options
% 14.87/2.49  
% 14.87/2.49  --resolution_flag                       false
% 14.87/2.49  --res_lit_sel                           adaptive
% 14.87/2.49  --res_lit_sel_side                      none
% 14.87/2.49  --res_ordering                          kbo
% 14.87/2.49  --res_to_prop_solver                    active
% 14.87/2.49  --res_prop_simpl_new                    false
% 14.87/2.49  --res_prop_simpl_given                  true
% 14.87/2.49  --res_passive_queue_type                priority_queues
% 14.87/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.87/2.49  --res_passive_queues_freq               [15;5]
% 14.87/2.49  --res_forward_subs                      full
% 14.87/2.49  --res_backward_subs                     full
% 14.87/2.49  --res_forward_subs_resolution           true
% 14.87/2.49  --res_backward_subs_resolution          true
% 14.87/2.49  --res_orphan_elimination                true
% 14.87/2.49  --res_time_limit                        2.
% 14.87/2.49  --res_out_proof                         true
% 14.87/2.49  
% 14.87/2.49  ------ Superposition Options
% 14.87/2.49  
% 14.87/2.49  --superposition_flag                    true
% 14.87/2.49  --sup_passive_queue_type                priority_queues
% 14.87/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.87/2.49  --sup_passive_queues_freq               [8;1;4]
% 14.87/2.49  --demod_completeness_check              fast
% 14.87/2.49  --demod_use_ground                      true
% 14.87/2.49  --sup_to_prop_solver                    passive
% 14.87/2.49  --sup_prop_simpl_new                    true
% 14.87/2.49  --sup_prop_simpl_given                  true
% 14.87/2.49  --sup_fun_splitting                     true
% 14.87/2.49  --sup_smt_interval                      50000
% 14.87/2.49  
% 14.87/2.49  ------ Superposition Simplification Setup
% 14.87/2.49  
% 14.87/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 14.87/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 14.87/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 14.87/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 14.87/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 14.87/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 14.87/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 14.87/2.49  --sup_immed_triv                        [TrivRules]
% 14.87/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.87/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.87/2.49  --sup_immed_bw_main                     []
% 14.87/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 14.87/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 14.87/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.87/2.49  --sup_input_bw                          []
% 14.87/2.49  
% 14.87/2.49  ------ Combination Options
% 14.87/2.49  
% 14.87/2.49  --comb_res_mult                         3
% 14.87/2.49  --comb_sup_mult                         2
% 14.87/2.49  --comb_inst_mult                        10
% 14.87/2.49  
% 14.87/2.49  ------ Debug Options
% 14.87/2.49  
% 14.87/2.49  --dbg_backtrace                         false
% 14.87/2.49  --dbg_dump_prop_clauses                 false
% 14.87/2.49  --dbg_dump_prop_clauses_file            -
% 14.87/2.49  --dbg_out_stat                          false
% 14.87/2.49  
% 14.87/2.49  
% 14.87/2.49  
% 14.87/2.49  
% 14.87/2.49  ------ Proving...
% 14.87/2.49  
% 14.87/2.49  
% 14.87/2.49  % SZS status Theorem for theBenchmark.p
% 14.87/2.49  
% 14.87/2.49   Resolution empty clause
% 14.87/2.49  
% 14.87/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 14.87/2.49  
% 14.87/2.49  fof(f12,conjecture,(
% 14.87/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f13,negated_conjecture,(
% 14.87/2.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 14.87/2.49    inference(negated_conjecture,[],[f12])).
% 14.87/2.49  
% 14.87/2.49  fof(f23,plain,(
% 14.87/2.49    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 14.87/2.49    inference(ennf_transformation,[],[f13])).
% 14.87/2.49  
% 14.87/2.49  fof(f24,plain,(
% 14.87/2.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 14.87/2.49    inference(flattening,[],[f23])).
% 14.87/2.49  
% 14.87/2.49  fof(f29,plain,(
% 14.87/2.49    ( ! [X0,X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v3_pre_topc(sK2,X0) & v1_tops_1(sK2,X0) & v1_tops_1(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 14.87/2.49    introduced(choice_axiom,[])).
% 14.87/2.49  
% 14.87/2.49  fof(f28,plain,(
% 14.87/2.49    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 14.87/2.49    introduced(choice_axiom,[])).
% 14.87/2.49  
% 14.87/2.49  fof(f27,plain,(
% 14.87/2.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 14.87/2.49    introduced(choice_axiom,[])).
% 14.87/2.49  
% 14.87/2.49  fof(f30,plain,(
% 14.87/2.49    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 14.87/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f29,f28,f27])).
% 14.87/2.49  
% 14.87/2.49  fof(f46,plain,(
% 14.87/2.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.87/2.49    inference(cnf_transformation,[],[f30])).
% 14.87/2.49  
% 14.87/2.49  fof(f8,axiom,(
% 14.87/2.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f18,plain,(
% 14.87/2.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 14.87/2.49    inference(ennf_transformation,[],[f8])).
% 14.87/2.49  
% 14.87/2.49  fof(f39,plain,(
% 14.87/2.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 14.87/2.49    inference(cnf_transformation,[],[f18])).
% 14.87/2.49  
% 14.87/2.49  fof(f7,axiom,(
% 14.87/2.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f17,plain,(
% 14.87/2.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 14.87/2.49    inference(ennf_transformation,[],[f7])).
% 14.87/2.49  
% 14.87/2.49  fof(f38,plain,(
% 14.87/2.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 14.87/2.49    inference(cnf_transformation,[],[f17])).
% 14.87/2.49  
% 14.87/2.49  fof(f45,plain,(
% 14.87/2.49    l1_pre_topc(sK0)),
% 14.87/2.49    inference(cnf_transformation,[],[f30])).
% 14.87/2.49  
% 14.87/2.49  fof(f6,axiom,(
% 14.87/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f25,plain,(
% 14.87/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 14.87/2.49    inference(nnf_transformation,[],[f6])).
% 14.87/2.49  
% 14.87/2.49  fof(f36,plain,(
% 14.87/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 14.87/2.49    inference(cnf_transformation,[],[f25])).
% 14.87/2.49  
% 14.87/2.49  fof(f2,axiom,(
% 14.87/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f14,plain,(
% 14.87/2.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 14.87/2.49    inference(ennf_transformation,[],[f2])).
% 14.87/2.49  
% 14.87/2.49  fof(f32,plain,(
% 14.87/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 14.87/2.49    inference(cnf_transformation,[],[f14])).
% 14.87/2.49  
% 14.87/2.49  fof(f3,axiom,(
% 14.87/2.49    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f33,plain,(
% 14.87/2.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 14.87/2.49    inference(cnf_transformation,[],[f3])).
% 14.87/2.49  
% 14.87/2.49  fof(f37,plain,(
% 14.87/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 14.87/2.49    inference(cnf_transformation,[],[f25])).
% 14.87/2.49  
% 14.87/2.49  fof(f47,plain,(
% 14.87/2.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 14.87/2.49    inference(cnf_transformation,[],[f30])).
% 14.87/2.49  
% 14.87/2.49  fof(f5,axiom,(
% 14.87/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f16,plain,(
% 14.87/2.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 14.87/2.49    inference(ennf_transformation,[],[f5])).
% 14.87/2.49  
% 14.87/2.49  fof(f35,plain,(
% 14.87/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 14.87/2.49    inference(cnf_transformation,[],[f16])).
% 14.87/2.49  
% 14.87/2.49  fof(f51,plain,(
% 14.87/2.49    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 14.87/2.49    inference(cnf_transformation,[],[f30])).
% 14.87/2.49  
% 14.87/2.49  fof(f10,axiom,(
% 14.87/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f20,plain,(
% 14.87/2.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.87/2.49    inference(ennf_transformation,[],[f10])).
% 14.87/2.49  
% 14.87/2.49  fof(f26,plain,(
% 14.87/2.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.87/2.49    inference(nnf_transformation,[],[f20])).
% 14.87/2.49  
% 14.87/2.49  fof(f42,plain,(
% 14.87/2.49    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 14.87/2.49    inference(cnf_transformation,[],[f26])).
% 14.87/2.49  
% 14.87/2.49  fof(f48,plain,(
% 14.87/2.49    v1_tops_1(sK1,sK0)),
% 14.87/2.49    inference(cnf_transformation,[],[f30])).
% 14.87/2.49  
% 14.87/2.49  fof(f11,axiom,(
% 14.87/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f21,plain,(
% 14.87/2.49    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 14.87/2.49    inference(ennf_transformation,[],[f11])).
% 14.87/2.49  
% 14.87/2.49  fof(f22,plain,(
% 14.87/2.49    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 14.87/2.49    inference(flattening,[],[f21])).
% 14.87/2.49  
% 14.87/2.49  fof(f43,plain,(
% 14.87/2.49    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 14.87/2.49    inference(cnf_transformation,[],[f22])).
% 14.87/2.49  
% 14.87/2.49  fof(f50,plain,(
% 14.87/2.49    v3_pre_topc(sK2,sK0)),
% 14.87/2.49    inference(cnf_transformation,[],[f30])).
% 14.87/2.49  
% 14.87/2.49  fof(f44,plain,(
% 14.87/2.49    v2_pre_topc(sK0)),
% 14.87/2.49    inference(cnf_transformation,[],[f30])).
% 14.87/2.49  
% 14.87/2.49  fof(f49,plain,(
% 14.87/2.49    v1_tops_1(sK2,sK0)),
% 14.87/2.49    inference(cnf_transformation,[],[f30])).
% 14.87/2.49  
% 14.87/2.49  fof(f41,plain,(
% 14.87/2.49    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 14.87/2.49    inference(cnf_transformation,[],[f26])).
% 14.87/2.49  
% 14.87/2.49  fof(f1,axiom,(
% 14.87/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f31,plain,(
% 14.87/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 14.87/2.49    inference(cnf_transformation,[],[f1])).
% 14.87/2.49  
% 14.87/2.49  fof(f9,axiom,(
% 14.87/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 14.87/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.87/2.49  
% 14.87/2.49  fof(f19,plain,(
% 14.87/2.49    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 14.87/2.49    inference(ennf_transformation,[],[f9])).
% 14.87/2.49  
% 14.87/2.49  fof(f40,plain,(
% 14.87/2.49    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 14.87/2.49    inference(cnf_transformation,[],[f19])).
% 14.87/2.49  
% 14.87/2.49  cnf(c_18,negated_conjecture,
% 14.87/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 14.87/2.49      inference(cnf_transformation,[],[f46]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1336,plain,
% 14.87/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 14.87/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_8,plain,
% 14.87/2.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f39]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_7,plain,
% 14.87/2.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f38]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_271,plain,
% 14.87/2.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 14.87/2.49      inference(resolution,[status(thm)],[c_8,c_7]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_19,negated_conjecture,
% 14.87/2.49      ( l1_pre_topc(sK0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f45]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_310,plain,
% 14.87/2.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 14.87/2.49      inference(resolution_lifted,[status(thm)],[c_271,c_19]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_311,plain,
% 14.87/2.49      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(unflattening,[status(thm)],[c_310]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1342,plain,
% 14.87/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 14.87/2.49      inference(light_normalisation,[status(thm)],[c_1336,c_311]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_6,plain,
% 14.87/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 14.87/2.49      inference(cnf_transformation,[],[f36]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1338,plain,
% 14.87/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 14.87/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 14.87/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1630,plain,
% 14.87/2.49      ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1342,c_1338]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1,plain,
% 14.87/2.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 14.87/2.49      inference(cnf_transformation,[],[f32]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1341,plain,
% 14.87/2.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 14.87/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1929,plain,
% 14.87/2.49      ( k2_xboole_0(sK1,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1630,c_1341]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_2,plain,
% 14.87/2.49      ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 14.87/2.49      inference(cnf_transformation,[],[f33]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1340,plain,
% 14.87/2.49      ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = iProver_top ),
% 14.87/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_2120,plain,
% 14.87/2.49      ( r1_tarski(k3_xboole_0(sK1,X0),k2_struct_0(sK0)) = iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1929,c_1340]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_5,plain,
% 14.87/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 14.87/2.49      inference(cnf_transformation,[],[f37]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1339,plain,
% 14.87/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 14.87/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 14.87/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_17,negated_conjecture,
% 14.87/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 14.87/2.49      inference(cnf_transformation,[],[f47]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1337,plain,
% 14.87/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 14.87/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1343,plain,
% 14.87/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 14.87/2.49      inference(light_normalisation,[status(thm)],[c_1337,c_311]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1631,plain,
% 14.87/2.49      ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1343,c_1338]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_4,plain,
% 14.87/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 14.87/2.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f35]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_155,plain,
% 14.87/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 14.87/2.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_156,plain,
% 14.87/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 14.87/2.49      inference(renaming,[status(thm)],[c_155]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_191,plain,
% 14.87/2.49      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 14.87/2.49      inference(bin_hyper_res,[status(thm)],[c_4,c_156]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1334,plain,
% 14.87/2.49      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 14.87/2.49      | r1_tarski(X2,X0) != iProver_top ),
% 14.87/2.49      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_25780,plain,
% 14.87/2.49      ( k9_subset_1(k2_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1631,c_1334]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_13,negated_conjecture,
% 14.87/2.49      ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f51]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_10,plain,
% 14.87/2.49      ( v1_tops_1(X0,X1)
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | ~ l1_pre_topc(X1)
% 14.87/2.49      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 14.87/2.49      inference(cnf_transformation,[],[f42]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_330,plain,
% 14.87/2.49      ( v1_tops_1(X0,X1)
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 14.87/2.49      | sK0 != X1 ),
% 14.87/2.49      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_331,plain,
% 14.87/2.49      ( v1_tops_1(X0,sK0)
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
% 14.87/2.49      inference(unflattening,[status(thm)],[c_330]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_398,plain,
% 14.87/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 14.87/2.49      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
% 14.87/2.49      | sK0 != sK0 ),
% 14.87/2.49      inference(resolution_lifted,[status(thm)],[c_13,c_331]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_399,plain,
% 14.87/2.49      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
% 14.87/2.49      inference(unflattening,[status(thm)],[c_398]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1331,plain,
% 14.87/2.49      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
% 14.87/2.49      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 14.87/2.49      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1349,plain,
% 14.87/2.49      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
% 14.87/2.49      | m1_subset_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 14.87/2.49      inference(light_normalisation,[status(thm)],[c_1331,c_311]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_26499,plain,
% 14.87/2.49      ( k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k2_struct_0(sK0)
% 14.87/2.49      | m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 14.87/2.49      inference(demodulation,[status(thm)],[c_25780,c_1349]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_25779,plain,
% 14.87/2.49      ( k9_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1630,c_1334]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_16,negated_conjecture,
% 14.87/2.49      ( v1_tops_1(sK1,sK0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f48]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_12,plain,
% 14.87/2.49      ( ~ v3_pre_topc(X0,X1)
% 14.87/2.49      | ~ v1_tops_1(X2,X1)
% 14.87/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | ~ v2_pre_topc(X1)
% 14.87/2.49      | ~ l1_pre_topc(X1)
% 14.87/2.49      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f43]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_14,negated_conjecture,
% 14.87/2.49      ( v3_pre_topc(sK2,sK0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f50]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_285,plain,
% 14.87/2.49      ( ~ v1_tops_1(X0,X1)
% 14.87/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | ~ v2_pre_topc(X1)
% 14.87/2.49      | ~ l1_pre_topc(X1)
% 14.87/2.49      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X0)) = k2_pre_topc(X1,X2)
% 14.87/2.49      | sK2 != X2
% 14.87/2.49      | sK0 != X1 ),
% 14.87/2.49      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_286,plain,
% 14.87/2.49      ( ~ v1_tops_1(X0,sK0)
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | ~ v2_pre_topc(sK0)
% 14.87/2.49      | ~ l1_pre_topc(sK0)
% 14.87/2.49      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 14.87/2.49      inference(unflattening,[status(thm)],[c_285]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_20,negated_conjecture,
% 14.87/2.49      ( v2_pre_topc(sK0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f44]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_290,plain,
% 14.87/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | ~ v1_tops_1(X0,sK0)
% 14.87/2.49      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 14.87/2.49      inference(global_propositional_subsumption,
% 14.87/2.49                [status(thm)],
% 14.87/2.49                [c_286,c_20,c_19,c_17]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_291,plain,
% 14.87/2.49      ( ~ v1_tops_1(X0,sK0)
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 14.87/2.49      inference(renaming,[status(thm)],[c_290]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_432,plain,
% 14.87/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2)
% 14.87/2.49      | sK1 != X0
% 14.87/2.49      | sK0 != sK0 ),
% 14.87/2.49      inference(resolution_lifted,[status(thm)],[c_16,c_291]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_433,plain,
% 14.87/2.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
% 14.87/2.49      inference(unflattening,[status(thm)],[c_432]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_435,plain,
% 14.87/2.49      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
% 14.87/2.49      inference(global_propositional_subsumption,[status(thm)],[c_433,c_18]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_15,negated_conjecture,
% 14.87/2.49      ( v1_tops_1(sK2,sK0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f49]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_11,plain,
% 14.87/2.49      ( ~ v1_tops_1(X0,X1)
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | ~ l1_pre_topc(X1)
% 14.87/2.49      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 14.87/2.49      inference(cnf_transformation,[],[f41]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_315,plain,
% 14.87/2.49      ( ~ v1_tops_1(X0,X1)
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 14.87/2.49      | sK0 != X1 ),
% 14.87/2.49      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_316,plain,
% 14.87/2.49      ( ~ v1_tops_1(X0,sK0)
% 14.87/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(unflattening,[status(thm)],[c_315]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_408,plain,
% 14.87/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 14.87/2.49      | sK2 != X0
% 14.87/2.49      | sK0 != sK0 ),
% 14.87/2.49      inference(resolution_lifted,[status(thm)],[c_15,c_316]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_409,plain,
% 14.87/2.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(unflattening,[status(thm)],[c_408]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_411,plain,
% 14.87/2.49      ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(global_propositional_subsumption,[status(thm)],[c_409,c_17]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1346,plain,
% 14.87/2.49      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(light_normalisation,[status(thm)],[c_435,c_311,c_411]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_26392,plain,
% 14.87/2.49      ( k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(demodulation,[status(thm)],[c_25779,c_1346]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_0,plain,
% 14.87/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 14.87/2.49      inference(cnf_transformation,[],[f31]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_9,plain,
% 14.87/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 14.87/2.49      | ~ l1_pre_topc(X1) ),
% 14.87/2.49      inference(cnf_transformation,[],[f40]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_345,plain,
% 14.87/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 14.87/2.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 14.87/2.49      | sK0 != X1 ),
% 14.87/2.49      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_346,plain,
% 14.87/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 14.87/2.49      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 14.87/2.49      inference(unflattening,[status(thm)],[c_345]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1333,plain,
% 14.87/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 14.87/2.49      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 14.87/2.49      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1348,plain,
% 14.87/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 14.87/2.49      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 14.87/2.49      inference(light_normalisation,[status(thm)],[c_1333,c_311]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_2038,plain,
% 14.87/2.49      ( r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
% 14.87/2.49      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1339,c_1348]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_2322,plain,
% 14.87/2.49      ( k2_xboole_0(X0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 14.87/2.49      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_2038,c_1341]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_2329,plain,
% 14.87/2.49      ( k2_xboole_0(k3_xboole_0(sK1,X0),k2_pre_topc(sK0,k3_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k3_xboole_0(sK1,X0)) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_2120,c_2322]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_2607,plain,
% 14.87/2.49      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X0),X1),k2_pre_topc(sK0,k3_xboole_0(sK1,X0))) = iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_2329,c_1340]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_3273,plain,
% 14.87/2.49      ( k2_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),X1),k2_pre_topc(sK0,k3_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k3_xboole_0(sK1,X0)) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_2607,c_1341]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_15921,plain,
% 14.87/2.49      ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),X1),k2_pre_topc(sK0,k3_xboole_0(X0,sK1))) = k2_pre_topc(sK0,k3_xboole_0(sK1,X0)) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_0,c_3273]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_16099,plain,
% 14.87/2.49      ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),k2_pre_topc(sK0,k3_xboole_0(X1,sK1))) = k2_pre_topc(sK0,k3_xboole_0(sK1,X1)) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_0,c_15921]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_26486,plain,
% 14.87/2.49      ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,sK1)),k2_struct_0(sK0)) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_26392,c_16099]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1966,plain,
% 14.87/2.49      ( k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1631,c_1341]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_2128,plain,
% 14.87/2.49      ( r1_tarski(k3_xboole_0(sK2,X0),k2_struct_0(sK0)) = iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1966,c_1340]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_2527,plain,
% 14.87/2.49      ( k2_xboole_0(k3_xboole_0(sK2,X0),k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_2128,c_1341]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_1703,plain,
% 14.87/2.49      ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_0,c_1340]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_2860,plain,
% 14.87/2.49      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k2_struct_0(sK0)) = iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_2527,c_1703]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_5156,plain,
% 14.87/2.49      ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_2860,c_1341]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_26491,plain,
% 14.87/2.49      ( k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) = k2_struct_0(sK0) ),
% 14.87/2.49      inference(demodulation,[status(thm)],[c_26486,c_5156]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_26507,plain,
% 14.87/2.49      ( k2_struct_0(sK0) != k2_struct_0(sK0)
% 14.87/2.49      | m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 14.87/2.49      inference(light_normalisation,[status(thm)],[c_26499,c_26491]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_26508,plain,
% 14.87/2.49      ( m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 14.87/2.49      inference(equality_resolution_simp,[status(thm)],[c_26507]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_28174,plain,
% 14.87/2.49      ( r1_tarski(k3_xboole_0(sK1,sK2),k2_struct_0(sK0)) != iProver_top ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_1339,c_26508]) ).
% 14.87/2.49  
% 14.87/2.49  cnf(c_48616,plain,
% 14.87/2.49      ( $false ),
% 14.87/2.49      inference(superposition,[status(thm)],[c_2120,c_28174]) ).
% 14.87/2.49  
% 14.87/2.49  
% 14.87/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 14.87/2.49  
% 14.87/2.49  ------                               Statistics
% 14.87/2.49  
% 14.87/2.49  ------ General
% 14.87/2.49  
% 14.87/2.49  abstr_ref_over_cycles:                  0
% 14.87/2.49  abstr_ref_under_cycles:                 0
% 14.87/2.49  gc_basic_clause_elim:                   0
% 14.87/2.49  forced_gc_time:                         0
% 14.87/2.49  parsing_time:                           0.007
% 14.87/2.49  unif_index_cands_time:                  0.
% 14.87/2.49  unif_index_add_time:                    0.
% 14.87/2.49  orderings_time:                         0.
% 14.87/2.49  out_proof_time:                         0.009
% 14.87/2.49  total_time:                             1.698
% 14.87/2.49  num_of_symbols:                         48
% 14.87/2.49  num_of_terms:                           34442
% 14.87/2.49  
% 14.87/2.49  ------ Preprocessing
% 14.87/2.49  
% 14.87/2.49  num_of_splits:                          0
% 14.87/2.49  num_of_split_atoms:                     0
% 14.87/2.49  num_of_reused_defs:                     0
% 14.87/2.49  num_eq_ax_congr_red:                    15
% 14.87/2.49  num_of_sem_filtered_clauses:            1
% 14.87/2.49  num_of_subtypes:                        0
% 14.87/2.49  monotx_restored_types:                  0
% 14.87/2.49  sat_num_of_epr_types:                   0
% 14.87/2.49  sat_num_of_non_cyclic_types:            0
% 14.87/2.49  sat_guarded_non_collapsed_types:        0
% 14.87/2.49  num_pure_diseq_elim:                    0
% 14.87/2.49  simp_replaced_by:                       0
% 14.87/2.49  res_preprocessed:                       97
% 14.87/2.49  prep_upred:                             0
% 14.87/2.49  prep_unflattend:                        61
% 14.87/2.49  smt_new_axioms:                         0
% 14.87/2.49  pred_elim_cands:                        2
% 14.87/2.49  pred_elim:                              5
% 14.87/2.49  pred_elim_cl:                           2
% 14.87/2.49  pred_elim_cycles:                       9
% 14.87/2.49  merged_defs:                            8
% 14.87/2.49  merged_defs_ncl:                        0
% 14.87/2.49  bin_hyper_res:                          10
% 14.87/2.49  prep_cycles:                            4
% 14.87/2.49  pred_elim_time:                         0.007
% 14.87/2.49  splitting_time:                         0.
% 14.87/2.49  sem_filter_time:                        0.
% 14.87/2.49  monotx_time:                            0.
% 14.87/2.49  subtype_inf_time:                       0.
% 14.87/2.49  
% 14.87/2.49  ------ Problem properties
% 14.87/2.49  
% 14.87/2.49  clauses:                                19
% 14.87/2.50  conjectures:                            2
% 14.87/2.50  epr:                                    0
% 14.87/2.50  horn:                                   19
% 14.87/2.50  ground:                                 10
% 14.87/2.50  unary:                                  11
% 14.87/2.50  binary:                                 7
% 14.87/2.50  lits:                                   28
% 14.87/2.50  lits_eq:                                14
% 14.87/2.50  fd_pure:                                0
% 14.87/2.50  fd_pseudo:                              0
% 14.87/2.50  fd_cond:                                0
% 14.87/2.50  fd_pseudo_cond:                         0
% 14.87/2.50  ac_symbols:                             0
% 14.87/2.50  
% 14.87/2.50  ------ Propositional Solver
% 14.87/2.50  
% 14.87/2.50  prop_solver_calls:                      34
% 14.87/2.50  prop_fast_solver_calls:                 1245
% 14.87/2.50  smt_solver_calls:                       0
% 14.87/2.50  smt_fast_solver_calls:                  0
% 14.87/2.50  prop_num_of_clauses:                    16540
% 14.87/2.50  prop_preprocess_simplified:             20539
% 14.87/2.50  prop_fo_subsumed:                       19
% 14.87/2.50  prop_solver_time:                       0.
% 14.87/2.50  smt_solver_time:                        0.
% 14.87/2.50  smt_fast_solver_time:                   0.
% 14.87/2.50  prop_fast_solver_time:                  0.
% 14.87/2.50  prop_unsat_core_time:                   0.
% 14.87/2.50  
% 14.87/2.50  ------ QBF
% 14.87/2.50  
% 14.87/2.50  qbf_q_res:                              0
% 14.87/2.50  qbf_num_tautologies:                    0
% 14.87/2.50  qbf_prep_cycles:                        0
% 14.87/2.50  
% 14.87/2.50  ------ BMC1
% 14.87/2.50  
% 14.87/2.50  bmc1_current_bound:                     -1
% 14.87/2.50  bmc1_last_solved_bound:                 -1
% 14.87/2.50  bmc1_unsat_core_size:                   -1
% 14.87/2.50  bmc1_unsat_core_parents_size:           -1
% 14.87/2.50  bmc1_merge_next_fun:                    0
% 14.87/2.50  bmc1_unsat_core_clauses_time:           0.
% 14.87/2.50  
% 14.87/2.50  ------ Instantiation
% 14.87/2.50  
% 14.87/2.50  inst_num_of_clauses:                    4733
% 14.87/2.50  inst_num_in_passive:                    1732
% 14.87/2.50  inst_num_in_active:                     1994
% 14.87/2.50  inst_num_in_unprocessed:                1009
% 14.87/2.50  inst_num_of_loops:                      2030
% 14.87/2.50  inst_num_of_learning_restarts:          0
% 14.87/2.50  inst_num_moves_active_passive:          29
% 14.87/2.50  inst_lit_activity:                      0
% 14.87/2.50  inst_lit_activity_moves:                0
% 14.87/2.50  inst_num_tautologies:                   0
% 14.87/2.50  inst_num_prop_implied:                  0
% 14.87/2.50  inst_num_existing_simplified:           0
% 14.87/2.50  inst_num_eq_res_simplified:             0
% 14.87/2.50  inst_num_child_elim:                    0
% 14.87/2.50  inst_num_of_dismatching_blockings:      1569
% 14.87/2.50  inst_num_of_non_proper_insts:           6919
% 14.87/2.50  inst_num_of_duplicates:                 0
% 14.87/2.50  inst_inst_num_from_inst_to_res:         0
% 14.87/2.50  inst_dismatching_checking_time:         0.
% 14.87/2.50  
% 14.87/2.50  ------ Resolution
% 14.87/2.50  
% 14.87/2.50  res_num_of_clauses:                     0
% 14.87/2.50  res_num_in_passive:                     0
% 14.87/2.50  res_num_in_active:                      0
% 14.87/2.50  res_num_of_loops:                       101
% 14.87/2.50  res_forward_subset_subsumed:            1096
% 14.87/2.50  res_backward_subset_subsumed:           4
% 14.87/2.50  res_forward_subsumed:                   0
% 14.87/2.50  res_backward_subsumed:                  0
% 14.87/2.50  res_forward_subsumption_resolution:     0
% 14.87/2.50  res_backward_subsumption_resolution:    0
% 14.87/2.50  res_clause_to_clause_subsumption:       58470
% 14.87/2.50  res_orphan_elimination:                 0
% 14.87/2.50  res_tautology_del:                      987
% 14.87/2.50  res_num_eq_res_simplified:              2
% 14.87/2.50  res_num_sel_changes:                    0
% 14.87/2.50  res_moves_from_active_to_pass:          0
% 14.87/2.50  
% 14.87/2.50  ------ Superposition
% 14.87/2.50  
% 14.87/2.50  sup_time_total:                         0.
% 14.87/2.50  sup_time_generating:                    0.
% 14.87/2.50  sup_time_sim_full:                      0.
% 14.87/2.50  sup_time_sim_immed:                     0.
% 14.87/2.50  
% 14.87/2.50  sup_num_of_clauses:                     3287
% 14.87/2.50  sup_num_in_active:                      387
% 14.87/2.50  sup_num_in_passive:                     2900
% 14.87/2.50  sup_num_of_loops:                       405
% 14.87/2.50  sup_fw_superposition:                   9060
% 14.87/2.50  sup_bw_superposition:                   4166
% 14.87/2.50  sup_immediate_simplified:               1916
% 14.87/2.50  sup_given_eliminated:                   0
% 14.87/2.50  comparisons_done:                       0
% 14.87/2.50  comparisons_avoided:                    0
% 14.87/2.50  
% 14.87/2.50  ------ Simplifications
% 14.87/2.50  
% 14.87/2.50  
% 14.87/2.50  sim_fw_subset_subsumed:                 17
% 14.87/2.50  sim_bw_subset_subsumed:                 7
% 14.87/2.50  sim_fw_subsumed:                        1042
% 14.87/2.50  sim_bw_subsumed:                        207
% 14.87/2.50  sim_fw_subsumption_res:                 0
% 14.87/2.50  sim_bw_subsumption_res:                 0
% 14.87/2.50  sim_tautology_del:                      10
% 14.87/2.50  sim_eq_tautology_del:                   98
% 14.87/2.50  sim_eq_res_simp:                        6
% 14.87/2.50  sim_fw_demodulated:                     499
% 14.87/2.50  sim_bw_demodulated:                     19
% 14.87/2.50  sim_light_normalised:                   396
% 14.87/2.50  sim_joinable_taut:                      0
% 14.87/2.50  sim_joinable_simp:                      0
% 14.87/2.50  sim_ac_normalised:                      0
% 14.87/2.50  sim_smt_subsumption:                    0
% 14.87/2.50  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:13:29 EST 2020

% Result     : Theorem 6.80s
% Output     : CNFRefutation 6.80s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 717 expanded)
%              Number of clauses        :   66 ( 269 expanded)
%              Number of leaves         :   14 ( 148 expanded)
%              Depth                    :   18
%              Number of atoms          :  334 (2501 expanded)
%              Number of equality atoms :  119 ( 318 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f72,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f72])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK4),X0)
          | ~ v4_pre_topc(sK4,X0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK4),X0)
          | v4_pre_topc(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),X1),sK3)
            | ~ v4_pre_topc(X1,sK3) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK3),X1),sK3)
            | v4_pre_topc(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3)
      | ~ v4_pre_topc(sK4,sK3) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3)
      | v4_pre_topc(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f73,f75,f74])).

fof(f117,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f76])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f116,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f108,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
              | ~ r1_xboole_0(X1,X2)
              | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
              | ~ r1_xboole_0(X1,X2)
              | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
      | ~ r1_xboole_0(X1,X2)
      | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f119,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3)
    | ~ v4_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f118,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3)
    | v4_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1668,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_22,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1686,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2468,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1686])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_297,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_378,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_297])).

cnf(c_1663,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_4669,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_2468,c_1663])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1694,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k3_subset_1(X2,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11129,plain,
    ( r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK3),sK4)) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4669,c_1694])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_2067,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2068,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2067])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_375,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_297])).

cnf(c_2413,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_2415,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2413])).

cnf(c_13897,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK3),sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11129,c_44,c_2068,c_2415])).

cnf(c_13898,plain,
    ( r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK3),sK4)) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13897])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1675,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6972,plain,
    ( k4_subset_1(u1_struct_0(sK3),sK4,k3_subset_1(u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1675])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_31,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_69,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2224,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_struct_0(sK3)
    | k4_subset_1(u1_struct_0(sK3),sK4,k3_subset_1(u1_struct_0(sK3),sK4)) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_7618,plain,
    ( k4_subset_1(u1_struct_0(sK3),sK4,k3_subset_1(u1_struct_0(sK3),sK4)) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6972,c_42,c_41,c_69,c_2224])).

cnf(c_37,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_struct_0(X2)
    | k4_subset_1(u1_struct_0(X2),X0,X1) != k2_struct_0(X2)
    | k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X0) = X1 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1672,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,X2) != k2_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
    | r1_xboole_0(X1,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8489,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4)
    | r1_xboole_0(sK4,k3_subset_1(u1_struct_0(sK3),sK4)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7618,c_1672])).

cnf(c_43,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_68,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_70,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_9742,plain,
    ( r1_xboole_0(sK4,k3_subset_1(u1_struct_0(sK3),sK4)) != iProver_top
    | k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8489,c_43,c_44,c_70,c_2068,c_2415])).

cnf(c_9743,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4)
    | r1_xboole_0(sK4,k3_subset_1(u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9742])).

cnf(c_13906,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4)
    | r1_tarski(sK4,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13898,c_9743])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_377,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_297])).

cnf(c_1664,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2052,plain,
    ( r1_tarski(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2827,plain,
    ( ~ r1_tarski(k1_xboole_0,X0)
    | k9_subset_1(X0,X1,X1) = X1 ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_3399,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1664,c_15,c_2052,c_2827])).

cnf(c_12,plain,
    ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1695,plain,
    ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9176,plain,
    ( r1_tarski(sK4,k3_subset_1(u1_struct_0(sK3),k9_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4),X0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4669,c_1695])).

cnf(c_9749,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK4,k3_subset_1(u1_struct_0(sK3),k9_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9176,c_44,c_2068,c_2415])).

cnf(c_9750,plain,
    ( r1_tarski(sK4,k3_subset_1(u1_struct_0(sK3),k9_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4),X0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9749])).

cnf(c_9757,plain,
    ( r1_tarski(sK4,k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_9750])).

cnf(c_9765,plain,
    ( r1_tarski(sK4,sK4) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9757,c_4669])).

cnf(c_14090,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13906,c_44,c_2068,c_2415,c_9765])).

cnf(c_28,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1680,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14137,plain,
    ( v4_pre_topc(sK4,sK3) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14090,c_1680])).

cnf(c_27,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1681,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14136,plain,
    ( v4_pre_topc(sK4,sK3) = iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14090,c_1681])).

cnf(c_39,negated_conjecture,
    ( ~ v4_pre_topc(sK4,sK3)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_46,plain,
    ( v4_pre_topc(sK4,sK3) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_40,negated_conjecture,
    ( v4_pre_topc(sK4,sK3)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_45,plain,
    ( v4_pre_topc(sK4,sK3) = iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14137,c_14136,c_46,c_45,c_44,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.80/1.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.80/1.53  
% 6.80/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.80/1.53  
% 6.80/1.53  ------  iProver source info
% 6.80/1.53  
% 6.80/1.53  git: date: 2020-06-30 10:37:57 +0100
% 6.80/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.80/1.53  git: non_committed_changes: false
% 6.80/1.53  git: last_make_outside_of_git: false
% 6.80/1.53  
% 6.80/1.53  ------ 
% 6.80/1.53  ------ Parsing...
% 6.80/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.80/1.53  
% 6.80/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 6.80/1.53  
% 6.80/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.80/1.53  
% 6.80/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.80/1.53  ------ Proving...
% 6.80/1.53  ------ Problem Properties 
% 6.80/1.53  
% 6.80/1.53  
% 6.80/1.53  clauses                                 41
% 6.80/1.53  conjectures                             4
% 6.80/1.53  EPR                                     6
% 6.80/1.53  Horn                                    35
% 6.80/1.53  unary                                   5
% 6.80/1.53  binary                                  14
% 6.80/1.53  lits                                    112
% 6.80/1.53  lits eq                                 12
% 6.80/1.53  fd_pure                                 0
% 6.80/1.53  fd_pseudo                               0
% 6.80/1.53  fd_cond                                 2
% 6.80/1.53  fd_pseudo_cond                          2
% 6.80/1.53  AC symbols                              0
% 6.80/1.53  
% 6.80/1.53  ------ Input Options Time Limit: Unbounded
% 6.80/1.53  
% 6.80/1.53  
% 6.80/1.53  ------ 
% 6.80/1.53  Current options:
% 6.80/1.53  ------ 
% 6.80/1.53  
% 6.80/1.53  
% 6.80/1.53  
% 6.80/1.53  
% 6.80/1.53  ------ Proving...
% 6.80/1.53  
% 6.80/1.53  
% 6.80/1.53  % SZS status Theorem for theBenchmark.p
% 6.80/1.53  
% 6.80/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 6.80/1.53  
% 6.80/1.53  fof(f28,conjecture,(
% 6.80/1.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f29,negated_conjecture,(
% 6.80/1.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 6.80/1.53    inference(negated_conjecture,[],[f28])).
% 6.80/1.53  
% 6.80/1.53  fof(f60,plain,(
% 6.80/1.53    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.80/1.53    inference(ennf_transformation,[],[f29])).
% 6.80/1.53  
% 6.80/1.53  fof(f72,plain,(
% 6.80/1.53    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.80/1.53    inference(nnf_transformation,[],[f60])).
% 6.80/1.53  
% 6.80/1.53  fof(f73,plain,(
% 6.80/1.53    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.80/1.53    inference(flattening,[],[f72])).
% 6.80/1.53  
% 6.80/1.53  fof(f75,plain,(
% 6.80/1.53    ( ! [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK4),X0) | ~v4_pre_topc(sK4,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK4),X0) | v4_pre_topc(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 6.80/1.53    introduced(choice_axiom,[])).
% 6.80/1.53  
% 6.80/1.53  fof(f74,plain,(
% 6.80/1.53    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK3),X1),sK3) | ~v4_pre_topc(X1,sK3)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK3),X1),sK3) | v4_pre_topc(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3))),
% 6.80/1.53    introduced(choice_axiom,[])).
% 6.80/1.53  
% 6.80/1.53  fof(f76,plain,(
% 6.80/1.53    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) | ~v4_pre_topc(sK4,sK3)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) | v4_pre_topc(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3)),
% 6.80/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f73,f75,f74])).
% 6.80/1.53  
% 6.80/1.53  fof(f117,plain,(
% 6.80/1.53    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 6.80/1.53    inference(cnf_transformation,[],[f76])).
% 6.80/1.53  
% 6.80/1.53  fof(f14,axiom,(
% 6.80/1.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f69,plain,(
% 6.80/1.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.80/1.53    inference(nnf_transformation,[],[f14])).
% 6.80/1.53  
% 6.80/1.53  fof(f98,plain,(
% 6.80/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.80/1.53    inference(cnf_transformation,[],[f69])).
% 6.80/1.53  
% 6.80/1.53  fof(f5,axiom,(
% 6.80/1.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f34,plain,(
% 6.80/1.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.80/1.53    inference(ennf_transformation,[],[f5])).
% 6.80/1.53  
% 6.80/1.53  fof(f84,plain,(
% 6.80/1.53    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.80/1.53    inference(cnf_transformation,[],[f34])).
% 6.80/1.53  
% 6.80/1.53  fof(f99,plain,(
% 6.80/1.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.80/1.53    inference(cnf_transformation,[],[f69])).
% 6.80/1.53  
% 6.80/1.53  fof(f9,axiom,(
% 6.80/1.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f38,plain,(
% 6.80/1.53    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.80/1.53    inference(ennf_transformation,[],[f9])).
% 6.80/1.53  
% 6.80/1.53  fof(f66,plain,(
% 6.80/1.53    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.80/1.53    inference(nnf_transformation,[],[f38])).
% 6.80/1.53  
% 6.80/1.53  fof(f91,plain,(
% 6.80/1.53    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.80/1.53    inference(cnf_transformation,[],[f66])).
% 6.80/1.53  
% 6.80/1.53  fof(f2,axiom,(
% 6.80/1.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f31,plain,(
% 6.80/1.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.80/1.53    inference(ennf_transformation,[],[f2])).
% 6.80/1.53  
% 6.80/1.53  fof(f81,plain,(
% 6.80/1.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.80/1.53    inference(cnf_transformation,[],[f31])).
% 6.80/1.53  
% 6.80/1.53  fof(f23,axiom,(
% 6.80/1.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f54,plain,(
% 6.80/1.53    ! [X0] : (! [X1] : (k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 6.80/1.53    inference(ennf_transformation,[],[f23])).
% 6.80/1.53  
% 6.80/1.53  fof(f110,plain,(
% 6.80/1.53    ( ! [X0,X1] : (k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 6.80/1.53    inference(cnf_transformation,[],[f54])).
% 6.80/1.53  
% 6.80/1.53  fof(f116,plain,(
% 6.80/1.53    l1_pre_topc(sK3)),
% 6.80/1.53    inference(cnf_transformation,[],[f76])).
% 6.80/1.53  
% 6.80/1.53  fof(f21,axiom,(
% 6.80/1.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f52,plain,(
% 6.80/1.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 6.80/1.53    inference(ennf_transformation,[],[f21])).
% 6.80/1.53  
% 6.80/1.53  fof(f108,plain,(
% 6.80/1.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 6.80/1.53    inference(cnf_transformation,[],[f52])).
% 6.80/1.53  
% 6.80/1.53  fof(f26,axiom,(
% 6.80/1.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f57,plain,(
% 6.80/1.53    ! [X0] : (! [X1] : (! [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | (~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 6.80/1.53    inference(ennf_transformation,[],[f26])).
% 6.80/1.53  
% 6.80/1.53  fof(f58,plain,(
% 6.80/1.53    ! [X0] : (! [X1] : (! [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | ~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 6.80/1.53    inference(flattening,[],[f57])).
% 6.80/1.53  
% 6.80/1.53  fof(f114,plain,(
% 6.80/1.53    ( ! [X2,X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | ~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 6.80/1.53    inference(cnf_transformation,[],[f58])).
% 6.80/1.53  
% 6.80/1.53  fof(f4,axiom,(
% 6.80/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f33,plain,(
% 6.80/1.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.80/1.53    inference(ennf_transformation,[],[f4])).
% 6.80/1.53  
% 6.80/1.53  fof(f83,plain,(
% 6.80/1.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.80/1.53    inference(cnf_transformation,[],[f33])).
% 6.80/1.53  
% 6.80/1.53  fof(f10,axiom,(
% 6.80/1.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f92,plain,(
% 6.80/1.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 6.80/1.53    inference(cnf_transformation,[],[f10])).
% 6.80/1.53  
% 6.80/1.53  fof(f8,axiom,(
% 6.80/1.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f37,plain,(
% 6.80/1.53    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.80/1.53    inference(ennf_transformation,[],[f8])).
% 6.80/1.53  
% 6.80/1.53  fof(f89,plain,(
% 6.80/1.53    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.80/1.53    inference(cnf_transformation,[],[f37])).
% 6.80/1.53  
% 6.80/1.53  fof(f18,axiom,(
% 6.80/1.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 6.80/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.80/1.53  
% 6.80/1.53  fof(f48,plain,(
% 6.80/1.53    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.80/1.53    inference(ennf_transformation,[],[f18])).
% 6.80/1.53  
% 6.80/1.53  fof(f71,plain,(
% 6.80/1.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.80/1.53    inference(nnf_transformation,[],[f48])).
% 6.80/1.53  
% 6.80/1.53  fof(f104,plain,(
% 6.80/1.53    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.80/1.53    inference(cnf_transformation,[],[f71])).
% 6.80/1.53  
% 6.80/1.53  fof(f105,plain,(
% 6.80/1.53    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.80/1.53    inference(cnf_transformation,[],[f71])).
% 6.80/1.53  
% 6.80/1.53  fof(f119,plain,(
% 6.80/1.53    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) | ~v4_pre_topc(sK4,sK3)),
% 6.80/1.53    inference(cnf_transformation,[],[f76])).
% 6.80/1.53  
% 6.80/1.53  fof(f118,plain,(
% 6.80/1.53    v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) | v4_pre_topc(sK4,sK3)),
% 6.80/1.53    inference(cnf_transformation,[],[f76])).
% 6.80/1.53  
% 6.80/1.53  cnf(c_41,negated_conjecture,
% 6.80/1.53      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 6.80/1.53      inference(cnf_transformation,[],[f117]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_1668,plain,
% 6.80/1.53      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 6.80/1.53      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_22,plain,
% 6.80/1.53      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.80/1.53      inference(cnf_transformation,[],[f98]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_1686,plain,
% 6.80/1.53      ( r1_tarski(X0,X1) = iProver_top
% 6.80/1.53      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 6.80/1.53      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_2468,plain,
% 6.80/1.53      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 6.80/1.53      inference(superposition,[status(thm)],[c_1668,c_1686]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_7,plain,
% 6.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.80/1.53      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 6.80/1.53      inference(cnf_transformation,[],[f84]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_21,plain,
% 6.80/1.53      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.80/1.53      inference(cnf_transformation,[],[f99]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_297,plain,
% 6.80/1.53      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.80/1.53      inference(prop_impl,[status(thm)],[c_21]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_378,plain,
% 6.80/1.53      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 6.80/1.53      inference(bin_hyper_res,[status(thm)],[c_7,c_297]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_1663,plain,
% 6.80/1.53      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 6.80/1.53      | r1_tarski(X1,X0) != iProver_top ),
% 6.80/1.53      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_4669,plain,
% 6.80/1.53      ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4)) = sK4 ),
% 6.80/1.53      inference(superposition,[status(thm)],[c_2468,c_1663]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_13,plain,
% 6.80/1.53      ( r1_xboole_0(X0,X1)
% 6.80/1.53      | ~ r1_tarski(X0,k3_subset_1(X2,X1))
% 6.80/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 6.80/1.53      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 6.80/1.53      inference(cnf_transformation,[],[f91]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_1694,plain,
% 6.80/1.53      ( r1_xboole_0(X0,X1) = iProver_top
% 6.80/1.53      | r1_tarski(X0,k3_subset_1(X2,X1)) != iProver_top
% 6.80/1.53      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 6.80/1.53      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 6.80/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_11129,plain,
% 6.80/1.53      ( r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK3),sK4)) = iProver_top
% 6.80/1.53      | r1_tarski(X0,sK4) != iProver_top
% 6.80/1.53      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.80/1.53      | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.80/1.53      inference(superposition,[status(thm)],[c_4669,c_1694]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_44,plain,
% 6.80/1.53      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 6.80/1.53      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_2067,plain,
% 6.80/1.53      ( r1_tarski(sK4,u1_struct_0(sK3))
% 6.80/1.53      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 6.80/1.53      inference(instantiation,[status(thm)],[c_22]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_2068,plain,
% 6.80/1.53      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top
% 6.80/1.53      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.80/1.53      inference(predicate_to_equality,[status(thm)],[c_2067]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_4,plain,
% 6.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.80/1.53      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 6.80/1.53      inference(cnf_transformation,[],[f81]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_375,plain,
% 6.80/1.53      ( ~ r1_tarski(X0,X1)
% 6.80/1.53      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 6.80/1.53      inference(bin_hyper_res,[status(thm)],[c_4,c_297]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_2413,plain,
% 6.80/1.53      ( ~ r1_tarski(sK4,u1_struct_0(sK3))
% 6.80/1.53      | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 6.80/1.53      inference(instantiation,[status(thm)],[c_375]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_2415,plain,
% 6.80/1.53      ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 6.80/1.53      | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 6.80/1.53      inference(predicate_to_equality,[status(thm)],[c_2413]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_13897,plain,
% 6.80/1.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.80/1.53      | r1_tarski(X0,sK4) != iProver_top
% 6.80/1.53      | r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK3),sK4)) = iProver_top ),
% 6.80/1.53      inference(global_propositional_subsumption,
% 6.80/1.53                [status(thm)],
% 6.80/1.53                [c_11129,c_44,c_2068,c_2415]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_13898,plain,
% 6.80/1.53      ( r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK3),sK4)) = iProver_top
% 6.80/1.53      | r1_tarski(X0,sK4) != iProver_top
% 6.80/1.53      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.80/1.53      inference(renaming,[status(thm)],[c_13897]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_33,plain,
% 6.80/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.80/1.53      | ~ l1_struct_0(X1)
% 6.80/1.53      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 6.80/1.53      inference(cnf_transformation,[],[f110]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_1675,plain,
% 6.80/1.53      ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
% 6.80/1.53      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.80/1.53      | l1_struct_0(X0) != iProver_top ),
% 6.80/1.53      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_6972,plain,
% 6.80/1.53      ( k4_subset_1(u1_struct_0(sK3),sK4,k3_subset_1(u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
% 6.80/1.53      | l1_struct_0(sK3) != iProver_top ),
% 6.80/1.53      inference(superposition,[status(thm)],[c_1668,c_1675]) ).
% 6.80/1.53  
% 6.80/1.53  cnf(c_42,negated_conjecture,
% 6.80/1.53      ( l1_pre_topc(sK3) ),
% 6.80/1.53      inference(cnf_transformation,[],[f116]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_31,plain,
% 6.80/1.54      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 6.80/1.54      inference(cnf_transformation,[],[f108]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_69,plain,
% 6.80/1.54      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 6.80/1.54      inference(instantiation,[status(thm)],[c_31]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_2224,plain,
% 6.80/1.54      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.80/1.54      | ~ l1_struct_0(sK3)
% 6.80/1.54      | k4_subset_1(u1_struct_0(sK3),sK4,k3_subset_1(u1_struct_0(sK3),sK4)) = k2_struct_0(sK3) ),
% 6.80/1.54      inference(instantiation,[status(thm)],[c_33]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_7618,plain,
% 6.80/1.54      ( k4_subset_1(u1_struct_0(sK3),sK4,k3_subset_1(u1_struct_0(sK3),sK4)) = k2_struct_0(sK3) ),
% 6.80/1.54      inference(global_propositional_subsumption,
% 6.80/1.54                [status(thm)],
% 6.80/1.54                [c_6972,c_42,c_41,c_69,c_2224]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_37,plain,
% 6.80/1.54      ( ~ r1_xboole_0(X0,X1)
% 6.80/1.54      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 6.80/1.54      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 6.80/1.54      | ~ l1_struct_0(X2)
% 6.80/1.54      | k4_subset_1(u1_struct_0(X2),X0,X1) != k2_struct_0(X2)
% 6.80/1.54      | k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X0) = X1 ),
% 6.80/1.54      inference(cnf_transformation,[],[f114]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_1672,plain,
% 6.80/1.54      ( k4_subset_1(u1_struct_0(X0),X1,X2) != k2_struct_0(X0)
% 6.80/1.54      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
% 6.80/1.54      | r1_xboole_0(X1,X2) != iProver_top
% 6.80/1.54      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.80/1.54      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.80/1.54      | l1_struct_0(X0) != iProver_top ),
% 6.80/1.54      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_8489,plain,
% 6.80/1.54      ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4)
% 6.80/1.54      | r1_xboole_0(sK4,k3_subset_1(u1_struct_0(sK3),sK4)) != iProver_top
% 6.80/1.54      | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.80/1.54      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.80/1.54      | l1_struct_0(sK3) != iProver_top ),
% 6.80/1.54      inference(superposition,[status(thm)],[c_7618,c_1672]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_43,plain,
% 6.80/1.54      ( l1_pre_topc(sK3) = iProver_top ),
% 6.80/1.54      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_68,plain,
% 6.80/1.54      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 6.80/1.54      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_70,plain,
% 6.80/1.54      ( l1_struct_0(sK3) = iProver_top
% 6.80/1.54      | l1_pre_topc(sK3) != iProver_top ),
% 6.80/1.54      inference(instantiation,[status(thm)],[c_68]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_9742,plain,
% 6.80/1.54      ( r1_xboole_0(sK4,k3_subset_1(u1_struct_0(sK3),sK4)) != iProver_top
% 6.80/1.54      | k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4) ),
% 6.80/1.54      inference(global_propositional_subsumption,
% 6.80/1.54                [status(thm)],
% 6.80/1.54                [c_8489,c_43,c_44,c_70,c_2068,c_2415]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_9743,plain,
% 6.80/1.54      ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4)
% 6.80/1.54      | r1_xboole_0(sK4,k3_subset_1(u1_struct_0(sK3),sK4)) != iProver_top ),
% 6.80/1.54      inference(renaming,[status(thm)],[c_9742]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_13906,plain,
% 6.80/1.54      ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4)
% 6.80/1.54      | r1_tarski(sK4,sK4) != iProver_top
% 6.80/1.54      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.80/1.54      inference(superposition,[status(thm)],[c_13898,c_9743]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_6,plain,
% 6.80/1.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 6.80/1.54      inference(cnf_transformation,[],[f83]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_377,plain,
% 6.80/1.54      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X2) = X2 ),
% 6.80/1.54      inference(bin_hyper_res,[status(thm)],[c_6,c_297]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_1664,plain,
% 6.80/1.54      ( k9_subset_1(X0,X1,X1) = X1 | r1_tarski(X2,X0) != iProver_top ),
% 6.80/1.54      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_15,plain,
% 6.80/1.54      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 6.80/1.54      inference(cnf_transformation,[],[f92]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_2052,plain,
% 6.80/1.54      ( r1_tarski(k1_xboole_0,X0)
% 6.80/1.54      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 6.80/1.54      inference(instantiation,[status(thm)],[c_22]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_2827,plain,
% 6.80/1.54      ( ~ r1_tarski(k1_xboole_0,X0) | k9_subset_1(X0,X1,X1) = X1 ),
% 6.80/1.54      inference(instantiation,[status(thm)],[c_377]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_3399,plain,
% 6.80/1.54      ( k9_subset_1(X0,X1,X1) = X1 ),
% 6.80/1.54      inference(global_propositional_subsumption,
% 6.80/1.54                [status(thm)],
% 6.80/1.54                [c_1664,c_15,c_2052,c_2827]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_12,plain,
% 6.80/1.54      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
% 6.80/1.54      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 6.80/1.54      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 6.80/1.54      inference(cnf_transformation,[],[f89]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_1695,plain,
% 6.80/1.54      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) = iProver_top
% 6.80/1.54      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 6.80/1.54      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 6.80/1.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_9176,plain,
% 6.80/1.54      ( r1_tarski(sK4,k3_subset_1(u1_struct_0(sK3),k9_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4),X0))) = iProver_top
% 6.80/1.54      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.80/1.54      | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.80/1.54      inference(superposition,[status(thm)],[c_4669,c_1695]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_9749,plain,
% 6.80/1.54      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.80/1.54      | r1_tarski(sK4,k3_subset_1(u1_struct_0(sK3),k9_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4),X0))) = iProver_top ),
% 6.80/1.54      inference(global_propositional_subsumption,
% 6.80/1.54                [status(thm)],
% 6.80/1.54                [c_9176,c_44,c_2068,c_2415]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_9750,plain,
% 6.80/1.54      ( r1_tarski(sK4,k3_subset_1(u1_struct_0(sK3),k9_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4),X0))) = iProver_top
% 6.80/1.54      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.80/1.54      inference(renaming,[status(thm)],[c_9749]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_9757,plain,
% 6.80/1.54      ( r1_tarski(sK4,k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4))) = iProver_top
% 6.80/1.54      | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.80/1.54      inference(superposition,[status(thm)],[c_3399,c_9750]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_9765,plain,
% 6.80/1.54      ( r1_tarski(sK4,sK4) = iProver_top
% 6.80/1.54      | m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.80/1.54      inference(light_normalisation,[status(thm)],[c_9757,c_4669]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_14090,plain,
% 6.80/1.54      ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK4) = k3_subset_1(u1_struct_0(sK3),sK4) ),
% 6.80/1.54      inference(global_propositional_subsumption,
% 6.80/1.54                [status(thm)],
% 6.80/1.54                [c_13906,c_44,c_2068,c_2415,c_9765]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_28,plain,
% 6.80/1.54      ( ~ v4_pre_topc(X0,X1)
% 6.80/1.54      | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1)
% 6.80/1.54      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.80/1.54      | ~ l1_pre_topc(X1) ),
% 6.80/1.54      inference(cnf_transformation,[],[f104]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_1680,plain,
% 6.80/1.54      ( v4_pre_topc(X0,X1) != iProver_top
% 6.80/1.54      | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1) = iProver_top
% 6.80/1.54      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 6.80/1.54      | l1_pre_topc(X1) != iProver_top ),
% 6.80/1.54      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_14137,plain,
% 6.80/1.54      ( v4_pre_topc(sK4,sK3) != iProver_top
% 6.80/1.54      | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) = iProver_top
% 6.80/1.54      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.80/1.54      | l1_pre_topc(sK3) != iProver_top ),
% 6.80/1.54      inference(superposition,[status(thm)],[c_14090,c_1680]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_27,plain,
% 6.80/1.54      ( v4_pre_topc(X0,X1)
% 6.80/1.54      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1)
% 6.80/1.54      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.80/1.54      | ~ l1_pre_topc(X1) ),
% 6.80/1.54      inference(cnf_transformation,[],[f105]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_1681,plain,
% 6.80/1.54      ( v4_pre_topc(X0,X1) = iProver_top
% 6.80/1.54      | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0),X1) != iProver_top
% 6.80/1.54      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 6.80/1.54      | l1_pre_topc(X1) != iProver_top ),
% 6.80/1.54      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_14136,plain,
% 6.80/1.54      ( v4_pre_topc(sK4,sK3) = iProver_top
% 6.80/1.54      | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) != iProver_top
% 6.80/1.54      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.80/1.54      | l1_pre_topc(sK3) != iProver_top ),
% 6.80/1.54      inference(superposition,[status(thm)],[c_14090,c_1681]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_39,negated_conjecture,
% 6.80/1.54      ( ~ v4_pre_topc(sK4,sK3)
% 6.80/1.54      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) ),
% 6.80/1.54      inference(cnf_transformation,[],[f119]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_46,plain,
% 6.80/1.54      ( v4_pre_topc(sK4,sK3) != iProver_top
% 6.80/1.54      | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) != iProver_top ),
% 6.80/1.54      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_40,negated_conjecture,
% 6.80/1.54      ( v4_pre_topc(sK4,sK3)
% 6.80/1.54      | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) ),
% 6.80/1.54      inference(cnf_transformation,[],[f118]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(c_45,plain,
% 6.80/1.54      ( v4_pre_topc(sK4,sK3) = iProver_top
% 6.80/1.54      | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK4),sK3) = iProver_top ),
% 6.80/1.54      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 6.80/1.54  
% 6.80/1.54  cnf(contradiction,plain,
% 6.80/1.54      ( $false ),
% 6.80/1.54      inference(minisat,
% 6.80/1.54                [status(thm)],
% 6.80/1.54                [c_14137,c_14136,c_46,c_45,c_44,c_43]) ).
% 6.80/1.54  
% 6.80/1.54  
% 6.80/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 6.80/1.54  
% 6.80/1.54  ------                               Statistics
% 6.80/1.54  
% 6.80/1.54  ------ Selected
% 6.80/1.54  
% 6.80/1.54  total_time:                             0.518
% 6.80/1.54  
%------------------------------------------------------------------------------

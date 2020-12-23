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
% DateTime   : Thu Dec  3 11:46:37 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 198 expanded)
%              Number of clauses        :   49 (  79 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :   19
%              Number of atoms          :  248 ( 446 expanded)
%              Number of equality atoms :   92 ( 128 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).

fof(f47,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_576,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_572,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_569,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_575,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1028,plain,
    ( k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_569,c_575])).

cnf(c_14,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_571,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1238,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k2_relat_1(k7_relat_1(sK2,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_571])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_573,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_864,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_569,c_573])).

cnf(c_1243,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k9_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1238,c_864])).

cnf(c_1244,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1243,c_864])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_574,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1241,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_relat_1(sK2,X2),X3) != iProver_top
    | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X2,X0)),k7_relat_1(X3,X1)) = iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_574])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_104,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_6,c_4])).

cnf(c_105,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_104])).

cnf(c_567,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_105])).

cnf(c_1656,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_864,c_567])).

cnf(c_1999,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_864,c_1656])).

cnf(c_2271,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k3_xboole_0(X2,X0)),k9_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X2),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1999])).

cnf(c_17,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18890,plain,
    ( v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X2)) != iProver_top
    | r1_tarski(k7_relat_1(sK2,X2),sK2) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k3_xboole_0(X2,X0)),k9_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2271,c_17])).

cnf(c_18891,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k3_xboole_0(X2,X0)),k9_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X2),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18890])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_577,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_570,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1102,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_577,c_570])).

cnf(c_18916,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k7_relat_1(sK2,sK0),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18891,c_1102])).

cnf(c_2960,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2961,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK1)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2960])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2963,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2964,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2963])).

cnf(c_20651,plain,
    ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k7_relat_1(sK2,sK0),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18916,c_17,c_2961,c_2964])).

cnf(c_20655,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_20651])).

cnf(c_20660,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_572,c_20655])).

cnf(c_22994,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20660,c_17])).

cnf(c_22998,plain,
    ( v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_576,c_22994])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22998,c_17])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.58/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.58/1.52  
% 7.58/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.52  
% 7.58/1.52  ------  iProver source info
% 7.58/1.52  
% 7.58/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.52  git: non_committed_changes: false
% 7.58/1.52  git: last_make_outside_of_git: false
% 7.58/1.52  
% 7.58/1.52  ------ 
% 7.58/1.52  
% 7.58/1.52  ------ Input Options
% 7.58/1.52  
% 7.58/1.52  --out_options                           all
% 7.58/1.52  --tptp_safe_out                         true
% 7.58/1.52  --problem_path                          ""
% 7.58/1.52  --include_path                          ""
% 7.58/1.52  --clausifier                            res/vclausify_rel
% 7.58/1.52  --clausifier_options                    ""
% 7.58/1.52  --stdin                                 false
% 7.58/1.52  --stats_out                             all
% 7.58/1.52  
% 7.58/1.52  ------ General Options
% 7.58/1.52  
% 7.58/1.52  --fof                                   false
% 7.58/1.52  --time_out_real                         305.
% 7.58/1.52  --time_out_virtual                      -1.
% 7.58/1.52  --symbol_type_check                     false
% 7.58/1.52  --clausify_out                          false
% 7.58/1.52  --sig_cnt_out                           false
% 7.58/1.52  --trig_cnt_out                          false
% 7.58/1.52  --trig_cnt_out_tolerance                1.
% 7.58/1.52  --trig_cnt_out_sk_spl                   false
% 7.58/1.52  --abstr_cl_out                          false
% 7.58/1.52  
% 7.58/1.52  ------ Global Options
% 7.58/1.52  
% 7.58/1.52  --schedule                              default
% 7.58/1.52  --add_important_lit                     false
% 7.58/1.52  --prop_solver_per_cl                    1000
% 7.58/1.52  --min_unsat_core                        false
% 7.58/1.52  --soft_assumptions                      false
% 7.58/1.52  --soft_lemma_size                       3
% 7.58/1.52  --prop_impl_unit_size                   0
% 7.58/1.52  --prop_impl_unit                        []
% 7.58/1.52  --share_sel_clauses                     true
% 7.58/1.52  --reset_solvers                         false
% 7.58/1.52  --bc_imp_inh                            [conj_cone]
% 7.58/1.52  --conj_cone_tolerance                   3.
% 7.58/1.52  --extra_neg_conj                        none
% 7.58/1.52  --large_theory_mode                     true
% 7.58/1.52  --prolific_symb_bound                   200
% 7.58/1.52  --lt_threshold                          2000
% 7.58/1.52  --clause_weak_htbl                      true
% 7.58/1.52  --gc_record_bc_elim                     false
% 7.58/1.52  
% 7.58/1.52  ------ Preprocessing Options
% 7.58/1.52  
% 7.58/1.52  --preprocessing_flag                    true
% 7.58/1.52  --time_out_prep_mult                    0.1
% 7.58/1.52  --splitting_mode                        input
% 7.58/1.52  --splitting_grd                         true
% 7.58/1.52  --splitting_cvd                         false
% 7.58/1.52  --splitting_cvd_svl                     false
% 7.58/1.52  --splitting_nvd                         32
% 7.58/1.52  --sub_typing                            true
% 7.58/1.52  --prep_gs_sim                           true
% 7.58/1.52  --prep_unflatten                        true
% 7.58/1.52  --prep_res_sim                          true
% 7.58/1.52  --prep_upred                            true
% 7.58/1.52  --prep_sem_filter                       exhaustive
% 7.58/1.52  --prep_sem_filter_out                   false
% 7.58/1.52  --pred_elim                             true
% 7.58/1.52  --res_sim_input                         true
% 7.58/1.52  --eq_ax_congr_red                       true
% 7.58/1.52  --pure_diseq_elim                       true
% 7.58/1.52  --brand_transform                       false
% 7.58/1.52  --non_eq_to_eq                          false
% 7.58/1.52  --prep_def_merge                        true
% 7.58/1.52  --prep_def_merge_prop_impl              false
% 7.58/1.52  --prep_def_merge_mbd                    true
% 7.58/1.52  --prep_def_merge_tr_red                 false
% 7.58/1.52  --prep_def_merge_tr_cl                  false
% 7.58/1.52  --smt_preprocessing                     true
% 7.58/1.52  --smt_ac_axioms                         fast
% 7.58/1.52  --preprocessed_out                      false
% 7.58/1.52  --preprocessed_stats                    false
% 7.58/1.52  
% 7.58/1.52  ------ Abstraction refinement Options
% 7.58/1.52  
% 7.58/1.52  --abstr_ref                             []
% 7.58/1.52  --abstr_ref_prep                        false
% 7.58/1.52  --abstr_ref_until_sat                   false
% 7.58/1.52  --abstr_ref_sig_restrict                funpre
% 7.58/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.52  --abstr_ref_under                       []
% 7.58/1.52  
% 7.58/1.52  ------ SAT Options
% 7.58/1.52  
% 7.58/1.52  --sat_mode                              false
% 7.58/1.52  --sat_fm_restart_options                ""
% 7.58/1.52  --sat_gr_def                            false
% 7.58/1.52  --sat_epr_types                         true
% 7.58/1.52  --sat_non_cyclic_types                  false
% 7.58/1.52  --sat_finite_models                     false
% 7.58/1.52  --sat_fm_lemmas                         false
% 7.58/1.52  --sat_fm_prep                           false
% 7.58/1.52  --sat_fm_uc_incr                        true
% 7.58/1.52  --sat_out_model                         small
% 7.58/1.52  --sat_out_clauses                       false
% 7.58/1.52  
% 7.58/1.52  ------ QBF Options
% 7.58/1.52  
% 7.58/1.52  --qbf_mode                              false
% 7.58/1.52  --qbf_elim_univ                         false
% 7.58/1.52  --qbf_dom_inst                          none
% 7.58/1.52  --qbf_dom_pre_inst                      false
% 7.58/1.52  --qbf_sk_in                             false
% 7.58/1.52  --qbf_pred_elim                         true
% 7.58/1.52  --qbf_split                             512
% 7.58/1.52  
% 7.58/1.52  ------ BMC1 Options
% 7.58/1.52  
% 7.58/1.52  --bmc1_incremental                      false
% 7.58/1.52  --bmc1_axioms                           reachable_all
% 7.58/1.52  --bmc1_min_bound                        0
% 7.58/1.52  --bmc1_max_bound                        -1
% 7.58/1.52  --bmc1_max_bound_default                -1
% 7.58/1.52  --bmc1_symbol_reachability              true
% 7.58/1.52  --bmc1_property_lemmas                  false
% 7.58/1.52  --bmc1_k_induction                      false
% 7.58/1.52  --bmc1_non_equiv_states                 false
% 7.58/1.52  --bmc1_deadlock                         false
% 7.58/1.52  --bmc1_ucm                              false
% 7.58/1.52  --bmc1_add_unsat_core                   none
% 7.58/1.52  --bmc1_unsat_core_children              false
% 7.58/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.52  --bmc1_out_stat                         full
% 7.58/1.52  --bmc1_ground_init                      false
% 7.58/1.52  --bmc1_pre_inst_next_state              false
% 7.58/1.52  --bmc1_pre_inst_state                   false
% 7.58/1.52  --bmc1_pre_inst_reach_state             false
% 7.58/1.52  --bmc1_out_unsat_core                   false
% 7.58/1.52  --bmc1_aig_witness_out                  false
% 7.58/1.52  --bmc1_verbose                          false
% 7.58/1.52  --bmc1_dump_clauses_tptp                false
% 7.58/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.52  --bmc1_dump_file                        -
% 7.58/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.52  --bmc1_ucm_extend_mode                  1
% 7.58/1.52  --bmc1_ucm_init_mode                    2
% 7.58/1.52  --bmc1_ucm_cone_mode                    none
% 7.58/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.52  --bmc1_ucm_relax_model                  4
% 7.58/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.52  --bmc1_ucm_layered_model                none
% 7.58/1.52  --bmc1_ucm_max_lemma_size               10
% 7.58/1.52  
% 7.58/1.52  ------ AIG Options
% 7.58/1.52  
% 7.58/1.52  --aig_mode                              false
% 7.58/1.52  
% 7.58/1.52  ------ Instantiation Options
% 7.58/1.52  
% 7.58/1.52  --instantiation_flag                    true
% 7.58/1.52  --inst_sos_flag                         true
% 7.58/1.52  --inst_sos_phase                        true
% 7.58/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.52  --inst_lit_sel_side                     num_symb
% 7.58/1.52  --inst_solver_per_active                1400
% 7.58/1.52  --inst_solver_calls_frac                1.
% 7.58/1.52  --inst_passive_queue_type               priority_queues
% 7.58/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.52  --inst_passive_queues_freq              [25;2]
% 7.58/1.52  --inst_dismatching                      true
% 7.58/1.52  --inst_eager_unprocessed_to_passive     true
% 7.58/1.52  --inst_prop_sim_given                   true
% 7.58/1.52  --inst_prop_sim_new                     false
% 7.58/1.52  --inst_subs_new                         false
% 7.58/1.52  --inst_eq_res_simp                      false
% 7.58/1.52  --inst_subs_given                       false
% 7.58/1.52  --inst_orphan_elimination               true
% 7.58/1.52  --inst_learning_loop_flag               true
% 7.58/1.52  --inst_learning_start                   3000
% 7.58/1.52  --inst_learning_factor                  2
% 7.58/1.52  --inst_start_prop_sim_after_learn       3
% 7.58/1.52  --inst_sel_renew                        solver
% 7.58/1.52  --inst_lit_activity_flag                true
% 7.58/1.52  --inst_restr_to_given                   false
% 7.58/1.52  --inst_activity_threshold               500
% 7.58/1.52  --inst_out_proof                        true
% 7.58/1.52  
% 7.58/1.52  ------ Resolution Options
% 7.58/1.52  
% 7.58/1.52  --resolution_flag                       true
% 7.58/1.52  --res_lit_sel                           adaptive
% 7.58/1.52  --res_lit_sel_side                      none
% 7.58/1.52  --res_ordering                          kbo
% 7.58/1.52  --res_to_prop_solver                    active
% 7.58/1.52  --res_prop_simpl_new                    false
% 7.58/1.52  --res_prop_simpl_given                  true
% 7.58/1.52  --res_passive_queue_type                priority_queues
% 7.58/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.52  --res_passive_queues_freq               [15;5]
% 7.58/1.52  --res_forward_subs                      full
% 7.58/1.52  --res_backward_subs                     full
% 7.58/1.52  --res_forward_subs_resolution           true
% 7.58/1.52  --res_backward_subs_resolution          true
% 7.58/1.52  --res_orphan_elimination                true
% 7.58/1.52  --res_time_limit                        2.
% 7.58/1.52  --res_out_proof                         true
% 7.58/1.52  
% 7.58/1.52  ------ Superposition Options
% 7.58/1.52  
% 7.58/1.52  --superposition_flag                    true
% 7.58/1.52  --sup_passive_queue_type                priority_queues
% 7.58/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.52  --demod_completeness_check              fast
% 7.58/1.52  --demod_use_ground                      true
% 7.58/1.52  --sup_to_prop_solver                    passive
% 7.58/1.52  --sup_prop_simpl_new                    true
% 7.58/1.52  --sup_prop_simpl_given                  true
% 7.58/1.52  --sup_fun_splitting                     true
% 7.58/1.52  --sup_smt_interval                      50000
% 7.58/1.52  
% 7.58/1.52  ------ Superposition Simplification Setup
% 7.58/1.52  
% 7.58/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.52  --sup_immed_triv                        [TrivRules]
% 7.58/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.52  --sup_immed_bw_main                     []
% 7.58/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.52  --sup_input_bw                          []
% 7.58/1.52  
% 7.58/1.52  ------ Combination Options
% 7.58/1.52  
% 7.58/1.52  --comb_res_mult                         3
% 7.58/1.52  --comb_sup_mult                         2
% 7.58/1.52  --comb_inst_mult                        10
% 7.58/1.52  
% 7.58/1.52  ------ Debug Options
% 7.58/1.52  
% 7.58/1.52  --dbg_backtrace                         false
% 7.58/1.52  --dbg_dump_prop_clauses                 false
% 7.58/1.52  --dbg_dump_prop_clauses_file            -
% 7.58/1.52  --dbg_out_stat                          false
% 7.58/1.52  ------ Parsing...
% 7.58/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.52  
% 7.58/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.58/1.52  
% 7.58/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.52  
% 7.58/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.52  ------ Proving...
% 7.58/1.52  ------ Problem Properties 
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  clauses                                 14
% 7.58/1.52  conjectures                             2
% 7.58/1.52  EPR                                     4
% 7.58/1.52  Horn                                    14
% 7.58/1.52  unary                                   3
% 7.58/1.52  binary                                  5
% 7.58/1.52  lits                                    33
% 7.58/1.52  lits eq                                 3
% 7.58/1.52  fd_pure                                 0
% 7.58/1.52  fd_pseudo                               0
% 7.58/1.52  fd_cond                                 0
% 7.58/1.52  fd_pseudo_cond                          1
% 7.58/1.52  AC symbols                              0
% 7.58/1.52  
% 7.58/1.52  ------ Schedule dynamic 5 is on 
% 7.58/1.52  
% 7.58/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  ------ 
% 7.58/1.52  Current options:
% 7.58/1.52  ------ 
% 7.58/1.52  
% 7.58/1.52  ------ Input Options
% 7.58/1.52  
% 7.58/1.52  --out_options                           all
% 7.58/1.52  --tptp_safe_out                         true
% 7.58/1.52  --problem_path                          ""
% 7.58/1.52  --include_path                          ""
% 7.58/1.52  --clausifier                            res/vclausify_rel
% 7.58/1.52  --clausifier_options                    ""
% 7.58/1.52  --stdin                                 false
% 7.58/1.52  --stats_out                             all
% 7.58/1.52  
% 7.58/1.52  ------ General Options
% 7.58/1.52  
% 7.58/1.52  --fof                                   false
% 7.58/1.52  --time_out_real                         305.
% 7.58/1.52  --time_out_virtual                      -1.
% 7.58/1.52  --symbol_type_check                     false
% 7.58/1.52  --clausify_out                          false
% 7.58/1.52  --sig_cnt_out                           false
% 7.58/1.52  --trig_cnt_out                          false
% 7.58/1.52  --trig_cnt_out_tolerance                1.
% 7.58/1.52  --trig_cnt_out_sk_spl                   false
% 7.58/1.52  --abstr_cl_out                          false
% 7.58/1.52  
% 7.58/1.52  ------ Global Options
% 7.58/1.52  
% 7.58/1.52  --schedule                              default
% 7.58/1.52  --add_important_lit                     false
% 7.58/1.52  --prop_solver_per_cl                    1000
% 7.58/1.52  --min_unsat_core                        false
% 7.58/1.52  --soft_assumptions                      false
% 7.58/1.52  --soft_lemma_size                       3
% 7.58/1.52  --prop_impl_unit_size                   0
% 7.58/1.52  --prop_impl_unit                        []
% 7.58/1.52  --share_sel_clauses                     true
% 7.58/1.52  --reset_solvers                         false
% 7.58/1.52  --bc_imp_inh                            [conj_cone]
% 7.58/1.52  --conj_cone_tolerance                   3.
% 7.58/1.52  --extra_neg_conj                        none
% 7.58/1.52  --large_theory_mode                     true
% 7.58/1.52  --prolific_symb_bound                   200
% 7.58/1.52  --lt_threshold                          2000
% 7.58/1.52  --clause_weak_htbl                      true
% 7.58/1.52  --gc_record_bc_elim                     false
% 7.58/1.52  
% 7.58/1.52  ------ Preprocessing Options
% 7.58/1.52  
% 7.58/1.52  --preprocessing_flag                    true
% 7.58/1.52  --time_out_prep_mult                    0.1
% 7.58/1.52  --splitting_mode                        input
% 7.58/1.52  --splitting_grd                         true
% 7.58/1.52  --splitting_cvd                         false
% 7.58/1.52  --splitting_cvd_svl                     false
% 7.58/1.52  --splitting_nvd                         32
% 7.58/1.52  --sub_typing                            true
% 7.58/1.52  --prep_gs_sim                           true
% 7.58/1.52  --prep_unflatten                        true
% 7.58/1.52  --prep_res_sim                          true
% 7.58/1.52  --prep_upred                            true
% 7.58/1.52  --prep_sem_filter                       exhaustive
% 7.58/1.52  --prep_sem_filter_out                   false
% 7.58/1.52  --pred_elim                             true
% 7.58/1.52  --res_sim_input                         true
% 7.58/1.52  --eq_ax_congr_red                       true
% 7.58/1.52  --pure_diseq_elim                       true
% 7.58/1.52  --brand_transform                       false
% 7.58/1.52  --non_eq_to_eq                          false
% 7.58/1.52  --prep_def_merge                        true
% 7.58/1.52  --prep_def_merge_prop_impl              false
% 7.58/1.52  --prep_def_merge_mbd                    true
% 7.58/1.52  --prep_def_merge_tr_red                 false
% 7.58/1.52  --prep_def_merge_tr_cl                  false
% 7.58/1.52  --smt_preprocessing                     true
% 7.58/1.52  --smt_ac_axioms                         fast
% 7.58/1.52  --preprocessed_out                      false
% 7.58/1.52  --preprocessed_stats                    false
% 7.58/1.52  
% 7.58/1.52  ------ Abstraction refinement Options
% 7.58/1.52  
% 7.58/1.52  --abstr_ref                             []
% 7.58/1.52  --abstr_ref_prep                        false
% 7.58/1.52  --abstr_ref_until_sat                   false
% 7.58/1.52  --abstr_ref_sig_restrict                funpre
% 7.58/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.52  --abstr_ref_under                       []
% 7.58/1.52  
% 7.58/1.52  ------ SAT Options
% 7.58/1.52  
% 7.58/1.52  --sat_mode                              false
% 7.58/1.52  --sat_fm_restart_options                ""
% 7.58/1.52  --sat_gr_def                            false
% 7.58/1.52  --sat_epr_types                         true
% 7.58/1.52  --sat_non_cyclic_types                  false
% 7.58/1.52  --sat_finite_models                     false
% 7.58/1.52  --sat_fm_lemmas                         false
% 7.58/1.52  --sat_fm_prep                           false
% 7.58/1.52  --sat_fm_uc_incr                        true
% 7.58/1.52  --sat_out_model                         small
% 7.58/1.52  --sat_out_clauses                       false
% 7.58/1.52  
% 7.58/1.52  ------ QBF Options
% 7.58/1.52  
% 7.58/1.52  --qbf_mode                              false
% 7.58/1.52  --qbf_elim_univ                         false
% 7.58/1.52  --qbf_dom_inst                          none
% 7.58/1.52  --qbf_dom_pre_inst                      false
% 7.58/1.52  --qbf_sk_in                             false
% 7.58/1.52  --qbf_pred_elim                         true
% 7.58/1.52  --qbf_split                             512
% 7.58/1.52  
% 7.58/1.52  ------ BMC1 Options
% 7.58/1.52  
% 7.58/1.52  --bmc1_incremental                      false
% 7.58/1.52  --bmc1_axioms                           reachable_all
% 7.58/1.52  --bmc1_min_bound                        0
% 7.58/1.52  --bmc1_max_bound                        -1
% 7.58/1.52  --bmc1_max_bound_default                -1
% 7.58/1.52  --bmc1_symbol_reachability              true
% 7.58/1.52  --bmc1_property_lemmas                  false
% 7.58/1.52  --bmc1_k_induction                      false
% 7.58/1.52  --bmc1_non_equiv_states                 false
% 7.58/1.52  --bmc1_deadlock                         false
% 7.58/1.52  --bmc1_ucm                              false
% 7.58/1.52  --bmc1_add_unsat_core                   none
% 7.58/1.52  --bmc1_unsat_core_children              false
% 7.58/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.52  --bmc1_out_stat                         full
% 7.58/1.52  --bmc1_ground_init                      false
% 7.58/1.52  --bmc1_pre_inst_next_state              false
% 7.58/1.52  --bmc1_pre_inst_state                   false
% 7.58/1.52  --bmc1_pre_inst_reach_state             false
% 7.58/1.52  --bmc1_out_unsat_core                   false
% 7.58/1.52  --bmc1_aig_witness_out                  false
% 7.58/1.52  --bmc1_verbose                          false
% 7.58/1.52  --bmc1_dump_clauses_tptp                false
% 7.58/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.52  --bmc1_dump_file                        -
% 7.58/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.52  --bmc1_ucm_extend_mode                  1
% 7.58/1.52  --bmc1_ucm_init_mode                    2
% 7.58/1.52  --bmc1_ucm_cone_mode                    none
% 7.58/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.52  --bmc1_ucm_relax_model                  4
% 7.58/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.52  --bmc1_ucm_layered_model                none
% 7.58/1.52  --bmc1_ucm_max_lemma_size               10
% 7.58/1.52  
% 7.58/1.52  ------ AIG Options
% 7.58/1.52  
% 7.58/1.52  --aig_mode                              false
% 7.58/1.52  
% 7.58/1.52  ------ Instantiation Options
% 7.58/1.52  
% 7.58/1.52  --instantiation_flag                    true
% 7.58/1.52  --inst_sos_flag                         true
% 7.58/1.52  --inst_sos_phase                        true
% 7.58/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.52  --inst_lit_sel_side                     none
% 7.58/1.52  --inst_solver_per_active                1400
% 7.58/1.52  --inst_solver_calls_frac                1.
% 7.58/1.52  --inst_passive_queue_type               priority_queues
% 7.58/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.52  --inst_passive_queues_freq              [25;2]
% 7.58/1.52  --inst_dismatching                      true
% 7.58/1.52  --inst_eager_unprocessed_to_passive     true
% 7.58/1.52  --inst_prop_sim_given                   true
% 7.58/1.52  --inst_prop_sim_new                     false
% 7.58/1.52  --inst_subs_new                         false
% 7.58/1.52  --inst_eq_res_simp                      false
% 7.58/1.52  --inst_subs_given                       false
% 7.58/1.52  --inst_orphan_elimination               true
% 7.58/1.52  --inst_learning_loop_flag               true
% 7.58/1.52  --inst_learning_start                   3000
% 7.58/1.52  --inst_learning_factor                  2
% 7.58/1.52  --inst_start_prop_sim_after_learn       3
% 7.58/1.52  --inst_sel_renew                        solver
% 7.58/1.52  --inst_lit_activity_flag                true
% 7.58/1.52  --inst_restr_to_given                   false
% 7.58/1.52  --inst_activity_threshold               500
% 7.58/1.52  --inst_out_proof                        true
% 7.58/1.52  
% 7.58/1.52  ------ Resolution Options
% 7.58/1.52  
% 7.58/1.52  --resolution_flag                       false
% 7.58/1.52  --res_lit_sel                           adaptive
% 7.58/1.52  --res_lit_sel_side                      none
% 7.58/1.52  --res_ordering                          kbo
% 7.58/1.52  --res_to_prop_solver                    active
% 7.58/1.52  --res_prop_simpl_new                    false
% 7.58/1.52  --res_prop_simpl_given                  true
% 7.58/1.52  --res_passive_queue_type                priority_queues
% 7.58/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.52  --res_passive_queues_freq               [15;5]
% 7.58/1.52  --res_forward_subs                      full
% 7.58/1.52  --res_backward_subs                     full
% 7.58/1.52  --res_forward_subs_resolution           true
% 7.58/1.52  --res_backward_subs_resolution          true
% 7.58/1.52  --res_orphan_elimination                true
% 7.58/1.52  --res_time_limit                        2.
% 7.58/1.52  --res_out_proof                         true
% 7.58/1.52  
% 7.58/1.52  ------ Superposition Options
% 7.58/1.52  
% 7.58/1.52  --superposition_flag                    true
% 7.58/1.52  --sup_passive_queue_type                priority_queues
% 7.58/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.52  --demod_completeness_check              fast
% 7.58/1.52  --demod_use_ground                      true
% 7.58/1.52  --sup_to_prop_solver                    passive
% 7.58/1.52  --sup_prop_simpl_new                    true
% 7.58/1.52  --sup_prop_simpl_given                  true
% 7.58/1.52  --sup_fun_splitting                     true
% 7.58/1.52  --sup_smt_interval                      50000
% 7.58/1.52  
% 7.58/1.52  ------ Superposition Simplification Setup
% 7.58/1.52  
% 7.58/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.52  --sup_immed_triv                        [TrivRules]
% 7.58/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.52  --sup_immed_bw_main                     []
% 7.58/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.52  --sup_input_bw                          []
% 7.58/1.52  
% 7.58/1.52  ------ Combination Options
% 7.58/1.52  
% 7.58/1.52  --comb_res_mult                         3
% 7.58/1.52  --comb_sup_mult                         2
% 7.58/1.52  --comb_inst_mult                        10
% 7.58/1.52  
% 7.58/1.52  ------ Debug Options
% 7.58/1.52  
% 7.58/1.52  --dbg_backtrace                         false
% 7.58/1.52  --dbg_dump_prop_clauses                 false
% 7.58/1.52  --dbg_dump_prop_clauses_file            -
% 7.58/1.52  --dbg_out_stat                          false
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  ------ Proving...
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  % SZS status Theorem for theBenchmark.p
% 7.58/1.52  
% 7.58/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.52  
% 7.58/1.52  fof(f5,axiom,(
% 7.58/1.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f17,plain,(
% 7.58/1.52    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.58/1.52    inference(ennf_transformation,[],[f5])).
% 7.58/1.52  
% 7.58/1.52  fof(f39,plain,(
% 7.58/1.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f17])).
% 7.58/1.52  
% 7.58/1.52  fof(f10,axiom,(
% 7.58/1.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f24,plain,(
% 7.58/1.52    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 7.58/1.52    inference(ennf_transformation,[],[f10])).
% 7.58/1.52  
% 7.58/1.52  fof(f45,plain,(
% 7.58/1.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f24])).
% 7.58/1.52  
% 7.58/1.52  fof(f12,conjecture,(
% 7.58/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f13,negated_conjecture,(
% 7.58/1.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 7.58/1.52    inference(negated_conjecture,[],[f12])).
% 7.58/1.52  
% 7.58/1.52  fof(f26,plain,(
% 7.58/1.52    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 7.58/1.52    inference(ennf_transformation,[],[f13])).
% 7.58/1.52  
% 7.58/1.52  fof(f30,plain,(
% 7.58/1.52    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 7.58/1.52    introduced(choice_axiom,[])).
% 7.58/1.52  
% 7.58/1.52  fof(f31,plain,(
% 7.58/1.52    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 7.58/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30])).
% 7.58/1.52  
% 7.58/1.52  fof(f47,plain,(
% 7.58/1.52    v1_relat_1(sK2)),
% 7.58/1.52    inference(cnf_transformation,[],[f31])).
% 7.58/1.52  
% 7.58/1.52  fof(f6,axiom,(
% 7.58/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f18,plain,(
% 7.58/1.52    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.58/1.52    inference(ennf_transformation,[],[f6])).
% 7.58/1.52  
% 7.58/1.52  fof(f40,plain,(
% 7.58/1.52    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f18])).
% 7.58/1.52  
% 7.58/1.52  fof(f11,axiom,(
% 7.58/1.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f25,plain,(
% 7.58/1.52    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.58/1.52    inference(ennf_transformation,[],[f11])).
% 7.58/1.52  
% 7.58/1.52  fof(f46,plain,(
% 7.58/1.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f25])).
% 7.58/1.52  
% 7.58/1.52  fof(f8,axiom,(
% 7.58/1.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f21,plain,(
% 7.58/1.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.58/1.52    inference(ennf_transformation,[],[f8])).
% 7.58/1.52  
% 7.58/1.52  fof(f42,plain,(
% 7.58/1.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f21])).
% 7.58/1.52  
% 7.58/1.52  fof(f7,axiom,(
% 7.58/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f19,plain,(
% 7.58/1.52    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 7.58/1.52    inference(ennf_transformation,[],[f7])).
% 7.58/1.52  
% 7.58/1.52  fof(f20,plain,(
% 7.58/1.52    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 7.58/1.52    inference(flattening,[],[f19])).
% 7.58/1.52  
% 7.58/1.52  fof(f41,plain,(
% 7.58/1.52    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f20])).
% 7.58/1.52  
% 7.58/1.52  fof(f9,axiom,(
% 7.58/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f22,plain,(
% 7.58/1.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.58/1.52    inference(ennf_transformation,[],[f9])).
% 7.58/1.52  
% 7.58/1.52  fof(f23,plain,(
% 7.58/1.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.58/1.52    inference(flattening,[],[f22])).
% 7.58/1.52  
% 7.58/1.52  fof(f44,plain,(
% 7.58/1.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f23])).
% 7.58/1.52  
% 7.58/1.52  fof(f4,axiom,(
% 7.58/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f16,plain,(
% 7.58/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.58/1.52    inference(ennf_transformation,[],[f4])).
% 7.58/1.52  
% 7.58/1.52  fof(f38,plain,(
% 7.58/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f16])).
% 7.58/1.52  
% 7.58/1.52  fof(f3,axiom,(
% 7.58/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f29,plain,(
% 7.58/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.58/1.52    inference(nnf_transformation,[],[f3])).
% 7.58/1.52  
% 7.58/1.52  fof(f37,plain,(
% 7.58/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f29])).
% 7.58/1.52  
% 7.58/1.52  fof(f2,axiom,(
% 7.58/1.52    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f14,plain,(
% 7.58/1.52    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.58/1.52    inference(ennf_transformation,[],[f2])).
% 7.58/1.52  
% 7.58/1.52  fof(f15,plain,(
% 7.58/1.52    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.58/1.52    inference(flattening,[],[f14])).
% 7.58/1.52  
% 7.58/1.52  fof(f35,plain,(
% 7.58/1.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.58/1.52    inference(cnf_transformation,[],[f15])).
% 7.58/1.52  
% 7.58/1.52  fof(f48,plain,(
% 7.58/1.52    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 7.58/1.52    inference(cnf_transformation,[],[f31])).
% 7.58/1.52  
% 7.58/1.52  fof(f1,axiom,(
% 7.58/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.58/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.52  
% 7.58/1.52  fof(f27,plain,(
% 7.58/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.58/1.52    inference(nnf_transformation,[],[f1])).
% 7.58/1.52  
% 7.58/1.52  fof(f28,plain,(
% 7.58/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.58/1.52    inference(flattening,[],[f27])).
% 7.58/1.52  
% 7.58/1.52  fof(f33,plain,(
% 7.58/1.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.58/1.52    inference(cnf_transformation,[],[f28])).
% 7.58/1.52  
% 7.58/1.52  fof(f49,plain,(
% 7.58/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.58/1.52    inference(equality_resolution,[],[f33])).
% 7.58/1.52  
% 7.58/1.52  cnf(c_7,plain,
% 7.58/1.52      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.58/1.52      inference(cnf_transformation,[],[f39]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_576,plain,
% 7.58/1.52      ( v1_relat_1(X0) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_13,plain,
% 7.58/1.52      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 7.58/1.52      inference(cnf_transformation,[],[f45]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_572,plain,
% 7.58/1.52      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 7.58/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_16,negated_conjecture,
% 7.58/1.52      ( v1_relat_1(sK2) ),
% 7.58/1.52      inference(cnf_transformation,[],[f47]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_569,plain,
% 7.58/1.52      ( v1_relat_1(sK2) = iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_8,plain,
% 7.58/1.52      ( ~ v1_relat_1(X0)
% 7.58/1.52      | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 7.58/1.52      inference(cnf_transformation,[],[f40]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_575,plain,
% 7.58/1.52      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2))
% 7.58/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1028,plain,
% 7.58/1.52      ( k7_relat_1(sK2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK2,X0),X1) ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_569,c_575]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_14,plain,
% 7.58/1.52      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 7.58/1.52      | ~ v1_relat_1(X0) ),
% 7.58/1.52      inference(cnf_transformation,[],[f46]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_571,plain,
% 7.58/1.52      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
% 7.58/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1238,plain,
% 7.58/1.52      ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k2_relat_1(k7_relat_1(sK2,X0))) = iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_1028,c_571]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_10,plain,
% 7.58/1.52      ( ~ v1_relat_1(X0)
% 7.58/1.52      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.58/1.52      inference(cnf_transformation,[],[f42]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_573,plain,
% 7.58/1.52      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.58/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_864,plain,
% 7.58/1.52      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_569,c_573]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1243,plain,
% 7.58/1.52      ( r1_tarski(k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))),k9_relat_1(sK2,X0)) = iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.58/1.52      inference(light_normalisation,[status(thm)],[c_1238,c_864]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1244,plain,
% 7.58/1.52      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0)) = iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 7.58/1.52      inference(demodulation,[status(thm)],[c_1243,c_864]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_9,plain,
% 7.58/1.52      ( ~ r1_tarski(X0,X1)
% 7.58/1.52      | ~ r1_tarski(X2,X3)
% 7.58/1.52      | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
% 7.58/1.52      | ~ v1_relat_1(X2)
% 7.58/1.52      | ~ v1_relat_1(X3) ),
% 7.58/1.52      inference(cnf_transformation,[],[f41]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_574,plain,
% 7.58/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.52      | r1_tarski(X2,X3) != iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) = iProver_top
% 7.58/1.52      | v1_relat_1(X2) != iProver_top
% 7.58/1.52      | v1_relat_1(X3) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1241,plain,
% 7.58/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(sK2,X2),X3) != iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(sK2,k3_xboole_0(X2,X0)),k7_relat_1(X3,X1)) = iProver_top
% 7.58/1.52      | v1_relat_1(X3) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X2)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_1028,c_574]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_11,plain,
% 7.58/1.52      ( ~ r1_tarski(X0,X1)
% 7.58/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.58/1.52      | ~ v1_relat_1(X0)
% 7.58/1.52      | ~ v1_relat_1(X1) ),
% 7.58/1.52      inference(cnf_transformation,[],[f44]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_6,plain,
% 7.58/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.52      | ~ v1_relat_1(X1)
% 7.58/1.52      | v1_relat_1(X0) ),
% 7.58/1.52      inference(cnf_transformation,[],[f38]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_4,plain,
% 7.58/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.58/1.52      inference(cnf_transformation,[],[f37]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_104,plain,
% 7.58/1.52      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.58/1.52      | ~ r1_tarski(X0,X1)
% 7.58/1.52      | ~ v1_relat_1(X1) ),
% 7.58/1.52      inference(global_propositional_subsumption,
% 7.58/1.52                [status(thm)],
% 7.58/1.52                [c_11,c_6,c_4]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_105,plain,
% 7.58/1.52      ( ~ r1_tarski(X0,X1)
% 7.58/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.58/1.52      | ~ v1_relat_1(X1) ),
% 7.58/1.52      inference(renaming,[status(thm)],[c_104]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_567,plain,
% 7.58/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.58/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_105]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1656,plain,
% 7.58/1.52      ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
% 7.58/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_864,c_567]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1999,plain,
% 7.58/1.52      ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_864,c_1656]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_2271,plain,
% 7.58/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.52      | r1_tarski(k9_relat_1(sK2,k3_xboole_0(X2,X0)),k9_relat_1(sK2,X1)) = iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(sK2,X2),sK2) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X2)) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top
% 7.58/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_1241,c_1999]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_17,plain,
% 7.58/1.52      ( v1_relat_1(sK2) = iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_18890,plain,
% 7.58/1.52      ( v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X2)) != iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(sK2,X2),sK2) != iProver_top
% 7.58/1.52      | r1_tarski(k9_relat_1(sK2,k3_xboole_0(X2,X0)),k9_relat_1(sK2,X1)) = iProver_top
% 7.58/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.58/1.52      inference(global_propositional_subsumption,
% 7.58/1.52                [status(thm)],
% 7.58/1.52                [c_2271,c_17]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_18891,plain,
% 7.58/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.52      | r1_tarski(k9_relat_1(sK2,k3_xboole_0(X2,X0)),k9_relat_1(sK2,X1)) = iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(sK2,X2),sK2) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X2)) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
% 7.58/1.52      inference(renaming,[status(thm)],[c_18890]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_3,plain,
% 7.58/1.52      ( ~ r1_tarski(X0,X1)
% 7.58/1.52      | ~ r1_tarski(X0,X2)
% 7.58/1.52      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 7.58/1.52      inference(cnf_transformation,[],[f35]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_577,plain,
% 7.58/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.52      | r1_tarski(X0,X2) != iProver_top
% 7.58/1.52      | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_15,negated_conjecture,
% 7.58/1.52      ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
% 7.58/1.52      inference(cnf_transformation,[],[f48]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_570,plain,
% 7.58/1.52      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1102,plain,
% 7.58/1.52      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) != iProver_top
% 7.58/1.52      | r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_577,c_570]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_18916,plain,
% 7.58/1.52      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(sK2,sK0),sK2) != iProver_top
% 7.58/1.52      | r1_tarski(sK1,sK1) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,sK1)) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_18891,c_1102]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_2960,plain,
% 7.58/1.52      ( v1_relat_1(k7_relat_1(sK2,sK1)) | ~ v1_relat_1(sK2) ),
% 7.58/1.52      inference(instantiation,[status(thm)],[c_7]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_2961,plain,
% 7.58/1.52      ( v1_relat_1(k7_relat_1(sK2,sK1)) = iProver_top
% 7.58/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_2960]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_1,plain,
% 7.58/1.52      ( r1_tarski(X0,X0) ),
% 7.58/1.52      inference(cnf_transformation,[],[f49]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_2963,plain,
% 7.58/1.52      ( r1_tarski(sK1,sK1) ),
% 7.58/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_2964,plain,
% 7.58/1.52      ( r1_tarski(sK1,sK1) = iProver_top ),
% 7.58/1.52      inference(predicate_to_equality,[status(thm)],[c_2963]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_20651,plain,
% 7.58/1.52      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) != iProver_top
% 7.58/1.52      | r1_tarski(k7_relat_1(sK2,sK0),sK2) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 7.58/1.52      inference(global_propositional_subsumption,
% 7.58/1.52                [status(thm)],
% 7.58/1.52                [c_18916,c_17,c_2961,c_2964]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_20655,plain,
% 7.58/1.52      ( r1_tarski(k7_relat_1(sK2,sK0),sK2) != iProver_top
% 7.58/1.52      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_1244,c_20651]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_20660,plain,
% 7.58/1.52      ( v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top
% 7.58/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_572,c_20655]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_22994,plain,
% 7.58/1.52      ( v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 7.58/1.52      inference(global_propositional_subsumption,
% 7.58/1.52                [status(thm)],
% 7.58/1.52                [c_20660,c_17]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(c_22998,plain,
% 7.58/1.52      ( v1_relat_1(sK2) != iProver_top ),
% 7.58/1.52      inference(superposition,[status(thm)],[c_576,c_22994]) ).
% 7.58/1.52  
% 7.58/1.52  cnf(contradiction,plain,
% 7.58/1.52      ( $false ),
% 7.58/1.52      inference(minisat,[status(thm)],[c_22998,c_17]) ).
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.52  
% 7.58/1.52  ------                               Statistics
% 7.58/1.52  
% 7.58/1.52  ------ General
% 7.58/1.52  
% 7.58/1.52  abstr_ref_over_cycles:                  0
% 7.58/1.52  abstr_ref_under_cycles:                 0
% 7.58/1.52  gc_basic_clause_elim:                   0
% 7.58/1.52  forced_gc_time:                         0
% 7.58/1.52  parsing_time:                           0.007
% 7.58/1.52  unif_index_cands_time:                  0.
% 7.58/1.52  unif_index_add_time:                    0.
% 7.58/1.52  orderings_time:                         0.
% 7.58/1.52  out_proof_time:                         0.01
% 7.58/1.52  total_time:                             0.832
% 7.58/1.52  num_of_symbols:                         43
% 7.58/1.52  num_of_terms:                           29277
% 7.58/1.52  
% 7.58/1.52  ------ Preprocessing
% 7.58/1.52  
% 7.58/1.52  num_of_splits:                          0
% 7.58/1.52  num_of_split_atoms:                     0
% 7.58/1.52  num_of_reused_defs:                     0
% 7.58/1.52  num_eq_ax_congr_red:                    5
% 7.58/1.52  num_of_sem_filtered_clauses:            1
% 7.58/1.52  num_of_subtypes:                        0
% 7.58/1.52  monotx_restored_types:                  0
% 7.58/1.52  sat_num_of_epr_types:                   0
% 7.58/1.52  sat_num_of_non_cyclic_types:            0
% 7.58/1.52  sat_guarded_non_collapsed_types:        0
% 7.58/1.52  num_pure_diseq_elim:                    0
% 7.58/1.52  simp_replaced_by:                       0
% 7.58/1.52  res_preprocessed:                       75
% 7.58/1.52  prep_upred:                             0
% 7.58/1.52  prep_unflattend:                        0
% 7.58/1.52  smt_new_axioms:                         0
% 7.58/1.52  pred_elim_cands:                        2
% 7.58/1.52  pred_elim:                              1
% 7.58/1.52  pred_elim_cl:                           2
% 7.58/1.52  pred_elim_cycles:                       3
% 7.58/1.52  merged_defs:                            2
% 7.58/1.52  merged_defs_ncl:                        0
% 7.58/1.52  bin_hyper_res:                          3
% 7.58/1.52  prep_cycles:                            4
% 7.58/1.52  pred_elim_time:                         0.001
% 7.58/1.52  splitting_time:                         0.
% 7.58/1.52  sem_filter_time:                        0.
% 7.58/1.52  monotx_time:                            0.
% 7.58/1.52  subtype_inf_time:                       0.
% 7.58/1.52  
% 7.58/1.52  ------ Problem properties
% 7.58/1.52  
% 7.58/1.52  clauses:                                14
% 7.58/1.52  conjectures:                            2
% 7.58/1.52  epr:                                    4
% 7.58/1.52  horn:                                   14
% 7.58/1.52  ground:                                 2
% 7.58/1.52  unary:                                  3
% 7.58/1.52  binary:                                 5
% 7.58/1.52  lits:                                   33
% 7.58/1.52  lits_eq:                                3
% 7.58/1.52  fd_pure:                                0
% 7.58/1.52  fd_pseudo:                              0
% 7.58/1.52  fd_cond:                                0
% 7.58/1.52  fd_pseudo_cond:                         1
% 7.58/1.52  ac_symbols:                             0
% 7.58/1.52  
% 7.58/1.52  ------ Propositional Solver
% 7.58/1.52  
% 7.58/1.52  prop_solver_calls:                      35
% 7.58/1.52  prop_fast_solver_calls:                 839
% 7.58/1.52  smt_solver_calls:                       0
% 7.58/1.52  smt_fast_solver_calls:                  0
% 7.58/1.52  prop_num_of_clauses:                    9341
% 7.58/1.52  prop_preprocess_simplified:             14856
% 7.58/1.52  prop_fo_subsumed:                       18
% 7.58/1.52  prop_solver_time:                       0.
% 7.58/1.52  smt_solver_time:                        0.
% 7.58/1.52  smt_fast_solver_time:                   0.
% 7.58/1.52  prop_fast_solver_time:                  0.
% 7.58/1.52  prop_unsat_core_time:                   0.001
% 7.58/1.52  
% 7.58/1.52  ------ QBF
% 7.58/1.52  
% 7.58/1.52  qbf_q_res:                              0
% 7.58/1.52  qbf_num_tautologies:                    0
% 7.58/1.52  qbf_prep_cycles:                        0
% 7.58/1.52  
% 7.58/1.52  ------ BMC1
% 7.58/1.52  
% 7.58/1.52  bmc1_current_bound:                     -1
% 7.58/1.52  bmc1_last_solved_bound:                 -1
% 7.58/1.52  bmc1_unsat_core_size:                   -1
% 7.58/1.52  bmc1_unsat_core_parents_size:           -1
% 7.58/1.52  bmc1_merge_next_fun:                    0
% 7.58/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.58/1.52  
% 7.58/1.52  ------ Instantiation
% 7.58/1.52  
% 7.58/1.52  inst_num_of_clauses:                    2130
% 7.58/1.52  inst_num_in_passive:                    814
% 7.58/1.52  inst_num_in_active:                     740
% 7.58/1.52  inst_num_in_unprocessed:                576
% 7.58/1.52  inst_num_of_loops:                      790
% 7.58/1.52  inst_num_of_learning_restarts:          0
% 7.58/1.52  inst_num_moves_active_passive:          46
% 7.58/1.52  inst_lit_activity:                      0
% 7.58/1.52  inst_lit_activity_moves:                1
% 7.58/1.52  inst_num_tautologies:                   0
% 7.58/1.52  inst_num_prop_implied:                  0
% 7.58/1.52  inst_num_existing_simplified:           0
% 7.58/1.52  inst_num_eq_res_simplified:             0
% 7.58/1.52  inst_num_child_elim:                    0
% 7.58/1.52  inst_num_of_dismatching_blockings:      1595
% 7.58/1.52  inst_num_of_non_proper_insts:           2699
% 7.58/1.52  inst_num_of_duplicates:                 0
% 7.58/1.52  inst_inst_num_from_inst_to_res:         0
% 7.58/1.52  inst_dismatching_checking_time:         0.
% 7.58/1.52  
% 7.58/1.52  ------ Resolution
% 7.58/1.52  
% 7.58/1.52  res_num_of_clauses:                     0
% 7.58/1.52  res_num_in_passive:                     0
% 7.58/1.52  res_num_in_active:                      0
% 7.58/1.52  res_num_of_loops:                       79
% 7.58/1.52  res_forward_subset_subsumed:            419
% 7.58/1.52  res_backward_subset_subsumed:           0
% 7.58/1.52  res_forward_subsumed:                   0
% 7.58/1.52  res_backward_subsumed:                  0
% 7.58/1.52  res_forward_subsumption_resolution:     0
% 7.58/1.52  res_backward_subsumption_resolution:    0
% 7.58/1.52  res_clause_to_clause_subsumption:       17819
% 7.58/1.52  res_orphan_elimination:                 0
% 7.58/1.52  res_tautology_del:                      219
% 7.58/1.52  res_num_eq_res_simplified:              0
% 7.58/1.52  res_num_sel_changes:                    0
% 7.58/1.52  res_moves_from_active_to_pass:          0
% 7.58/1.52  
% 7.58/1.52  ------ Superposition
% 7.58/1.52  
% 7.58/1.52  sup_time_total:                         0.
% 7.58/1.52  sup_time_generating:                    0.
% 7.58/1.52  sup_time_sim_full:                      0.
% 7.58/1.52  sup_time_sim_immed:                     0.
% 7.58/1.52  
% 7.58/1.52  sup_num_of_clauses:                     1066
% 7.58/1.52  sup_num_in_active:                      150
% 7.58/1.52  sup_num_in_passive:                     916
% 7.58/1.52  sup_num_of_loops:                       157
% 7.58/1.52  sup_fw_superposition:                   1381
% 7.58/1.52  sup_bw_superposition:                   2006
% 7.58/1.52  sup_immediate_simplified:               2441
% 7.58/1.52  sup_given_eliminated:                   1
% 7.58/1.52  comparisons_done:                       0
% 7.58/1.52  comparisons_avoided:                    0
% 7.58/1.52  
% 7.58/1.52  ------ Simplifications
% 7.58/1.52  
% 7.58/1.52  
% 7.58/1.52  sim_fw_subset_subsumed:                 3
% 7.58/1.52  sim_bw_subset_subsumed:                 7
% 7.58/1.52  sim_fw_subsumed:                        605
% 7.58/1.52  sim_bw_subsumed:                        18
% 7.58/1.52  sim_fw_subsumption_res:                 0
% 7.58/1.52  sim_bw_subsumption_res:                 0
% 7.58/1.52  sim_tautology_del:                      4
% 7.58/1.52  sim_eq_tautology_del:                   166
% 7.58/1.52  sim_eq_res_simp:                        0
% 7.58/1.52  sim_fw_demodulated:                     2609
% 7.58/1.52  sim_bw_demodulated:                     5
% 7.58/1.52  sim_light_normalised:                   822
% 7.58/1.52  sim_joinable_taut:                      0
% 7.58/1.52  sim_joinable_simp:                      0
% 7.58/1.52  sim_ac_normalised:                      0
% 7.58/1.52  sim_smt_subsumption:                    0
% 7.58/1.52  
%------------------------------------------------------------------------------

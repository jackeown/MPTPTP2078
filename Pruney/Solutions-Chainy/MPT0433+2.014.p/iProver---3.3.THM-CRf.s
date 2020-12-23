%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:53 EST 2020

% Result     : Theorem 39.85s
% Output     : CNFRefutation 39.85s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 406 expanded)
%              Number of clauses        :   55 ( 179 expanded)
%              Number of leaves         :   13 (  83 expanded)
%              Depth                    :   19
%              Number of atoms          :  186 ( 935 expanded)
%              Number of equality atoms :   68 ( 262 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28,f27])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_597,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_595,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_949,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_597,c_595])).

cnf(c_8,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_591,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1451,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_949,c_591])).

cnf(c_1452,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1451,c_949])).

cnf(c_1632,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1452,c_595])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_586,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_585,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_594,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_139,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_140,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_139])).

cnf(c_167,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_140])).

cnf(c_584,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_1064,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_584])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_588,plain,
    ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3364,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(X0,X1)),k1_relat_1(X2)) = k1_relat_1(k2_xboole_0(k3_xboole_0(X0,X1),X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_588])).

cnf(c_122384,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_3364])).

cnf(c_125636,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1)) ),
    inference(superposition,[status(thm)],[c_586,c_122384])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_590,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_952,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_590,c_595])).

cnf(c_125709,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1))) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_125636,c_952])).

cnf(c_125817,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1))) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_125709,c_125636])).

cnf(c_141951,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_1632,c_125817])).

cnf(c_142065,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(demodulation,[status(thm)],[c_141951,c_1632,c_125636])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_596,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_142346,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_142065,c_596])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_593,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_587,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2112,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_587])).

cnf(c_175100,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_142346,c_2112])).

cnf(c_20,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_694,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_695,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_125710,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_125636,c_590])).

cnf(c_128853,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_125710])).

cnf(c_175684,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_175100,c_20,c_695,c_128853])).

cnf(c_125637,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK0)) ),
    inference(superposition,[status(thm)],[c_585,c_122384])).

cnf(c_950,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_594,c_595])).

cnf(c_125667,plain,
    ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK0)) = k1_relat_1(sK0) ),
    inference(demodulation,[status(thm)],[c_125637,c_950])).

cnf(c_126480,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_125667,c_590])).

cnf(c_175689,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_175684,c_126480])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.85/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.85/5.49  
% 39.85/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.85/5.49  
% 39.85/5.49  ------  iProver source info
% 39.85/5.49  
% 39.85/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.85/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.85/5.49  git: non_committed_changes: false
% 39.85/5.49  git: last_make_outside_of_git: false
% 39.85/5.49  
% 39.85/5.49  ------ 
% 39.85/5.49  
% 39.85/5.49  ------ Input Options
% 39.85/5.49  
% 39.85/5.49  --out_options                           all
% 39.85/5.49  --tptp_safe_out                         true
% 39.85/5.49  --problem_path                          ""
% 39.85/5.49  --include_path                          ""
% 39.85/5.49  --clausifier                            res/vclausify_rel
% 39.85/5.49  --clausifier_options                    --mode clausify
% 39.85/5.49  --stdin                                 false
% 39.85/5.49  --stats_out                             all
% 39.85/5.49  
% 39.85/5.49  ------ General Options
% 39.85/5.49  
% 39.85/5.49  --fof                                   false
% 39.85/5.49  --time_out_real                         305.
% 39.85/5.49  --time_out_virtual                      -1.
% 39.85/5.49  --symbol_type_check                     false
% 39.85/5.49  --clausify_out                          false
% 39.85/5.49  --sig_cnt_out                           false
% 39.85/5.49  --trig_cnt_out                          false
% 39.85/5.49  --trig_cnt_out_tolerance                1.
% 39.85/5.49  --trig_cnt_out_sk_spl                   false
% 39.85/5.49  --abstr_cl_out                          false
% 39.85/5.49  
% 39.85/5.49  ------ Global Options
% 39.85/5.49  
% 39.85/5.49  --schedule                              default
% 39.85/5.49  --add_important_lit                     false
% 39.85/5.49  --prop_solver_per_cl                    1000
% 39.85/5.49  --min_unsat_core                        false
% 39.85/5.49  --soft_assumptions                      false
% 39.85/5.49  --soft_lemma_size                       3
% 39.85/5.49  --prop_impl_unit_size                   0
% 39.85/5.49  --prop_impl_unit                        []
% 39.85/5.49  --share_sel_clauses                     true
% 39.85/5.49  --reset_solvers                         false
% 39.85/5.49  --bc_imp_inh                            [conj_cone]
% 39.85/5.49  --conj_cone_tolerance                   3.
% 39.85/5.49  --extra_neg_conj                        none
% 39.85/5.49  --large_theory_mode                     true
% 39.85/5.49  --prolific_symb_bound                   200
% 39.85/5.49  --lt_threshold                          2000
% 39.85/5.49  --clause_weak_htbl                      true
% 39.85/5.49  --gc_record_bc_elim                     false
% 39.85/5.49  
% 39.85/5.49  ------ Preprocessing Options
% 39.85/5.49  
% 39.85/5.49  --preprocessing_flag                    true
% 39.85/5.49  --time_out_prep_mult                    0.1
% 39.85/5.49  --splitting_mode                        input
% 39.85/5.49  --splitting_grd                         true
% 39.85/5.49  --splitting_cvd                         false
% 39.85/5.49  --splitting_cvd_svl                     false
% 39.85/5.49  --splitting_nvd                         32
% 39.85/5.49  --sub_typing                            true
% 39.85/5.49  --prep_gs_sim                           true
% 39.85/5.49  --prep_unflatten                        true
% 39.85/5.49  --prep_res_sim                          true
% 39.85/5.49  --prep_upred                            true
% 39.85/5.49  --prep_sem_filter                       exhaustive
% 39.85/5.49  --prep_sem_filter_out                   false
% 39.85/5.49  --pred_elim                             true
% 39.85/5.49  --res_sim_input                         true
% 39.85/5.49  --eq_ax_congr_red                       true
% 39.85/5.49  --pure_diseq_elim                       true
% 39.85/5.49  --brand_transform                       false
% 39.85/5.49  --non_eq_to_eq                          false
% 39.85/5.49  --prep_def_merge                        true
% 39.85/5.49  --prep_def_merge_prop_impl              false
% 39.85/5.49  --prep_def_merge_mbd                    true
% 39.85/5.49  --prep_def_merge_tr_red                 false
% 39.85/5.49  --prep_def_merge_tr_cl                  false
% 39.85/5.49  --smt_preprocessing                     true
% 39.85/5.49  --smt_ac_axioms                         fast
% 39.85/5.49  --preprocessed_out                      false
% 39.85/5.49  --preprocessed_stats                    false
% 39.85/5.49  
% 39.85/5.49  ------ Abstraction refinement Options
% 39.85/5.49  
% 39.85/5.49  --abstr_ref                             []
% 39.85/5.49  --abstr_ref_prep                        false
% 39.85/5.49  --abstr_ref_until_sat                   false
% 39.85/5.49  --abstr_ref_sig_restrict                funpre
% 39.85/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.85/5.49  --abstr_ref_under                       []
% 39.85/5.49  
% 39.85/5.49  ------ SAT Options
% 39.85/5.49  
% 39.85/5.49  --sat_mode                              false
% 39.85/5.49  --sat_fm_restart_options                ""
% 39.85/5.49  --sat_gr_def                            false
% 39.85/5.49  --sat_epr_types                         true
% 39.85/5.49  --sat_non_cyclic_types                  false
% 39.85/5.49  --sat_finite_models                     false
% 39.85/5.49  --sat_fm_lemmas                         false
% 39.85/5.49  --sat_fm_prep                           false
% 39.85/5.49  --sat_fm_uc_incr                        true
% 39.85/5.49  --sat_out_model                         small
% 39.85/5.49  --sat_out_clauses                       false
% 39.85/5.49  
% 39.85/5.49  ------ QBF Options
% 39.85/5.49  
% 39.85/5.49  --qbf_mode                              false
% 39.85/5.49  --qbf_elim_univ                         false
% 39.85/5.49  --qbf_dom_inst                          none
% 39.85/5.49  --qbf_dom_pre_inst                      false
% 39.85/5.49  --qbf_sk_in                             false
% 39.85/5.49  --qbf_pred_elim                         true
% 39.85/5.49  --qbf_split                             512
% 39.85/5.49  
% 39.85/5.49  ------ BMC1 Options
% 39.85/5.49  
% 39.85/5.49  --bmc1_incremental                      false
% 39.85/5.49  --bmc1_axioms                           reachable_all
% 39.85/5.49  --bmc1_min_bound                        0
% 39.85/5.49  --bmc1_max_bound                        -1
% 39.85/5.49  --bmc1_max_bound_default                -1
% 39.85/5.49  --bmc1_symbol_reachability              true
% 39.85/5.49  --bmc1_property_lemmas                  false
% 39.85/5.49  --bmc1_k_induction                      false
% 39.85/5.49  --bmc1_non_equiv_states                 false
% 39.85/5.49  --bmc1_deadlock                         false
% 39.85/5.49  --bmc1_ucm                              false
% 39.85/5.49  --bmc1_add_unsat_core                   none
% 39.85/5.49  --bmc1_unsat_core_children              false
% 39.85/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.85/5.49  --bmc1_out_stat                         full
% 39.85/5.49  --bmc1_ground_init                      false
% 39.85/5.49  --bmc1_pre_inst_next_state              false
% 39.85/5.49  --bmc1_pre_inst_state                   false
% 39.85/5.49  --bmc1_pre_inst_reach_state             false
% 39.85/5.49  --bmc1_out_unsat_core                   false
% 39.85/5.49  --bmc1_aig_witness_out                  false
% 39.85/5.49  --bmc1_verbose                          false
% 39.85/5.49  --bmc1_dump_clauses_tptp                false
% 39.85/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.85/5.49  --bmc1_dump_file                        -
% 39.85/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.85/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.85/5.49  --bmc1_ucm_extend_mode                  1
% 39.85/5.49  --bmc1_ucm_init_mode                    2
% 39.85/5.49  --bmc1_ucm_cone_mode                    none
% 39.85/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.85/5.49  --bmc1_ucm_relax_model                  4
% 39.85/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.85/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.85/5.49  --bmc1_ucm_layered_model                none
% 39.85/5.49  --bmc1_ucm_max_lemma_size               10
% 39.85/5.49  
% 39.85/5.49  ------ AIG Options
% 39.85/5.49  
% 39.85/5.49  --aig_mode                              false
% 39.85/5.49  
% 39.85/5.49  ------ Instantiation Options
% 39.85/5.49  
% 39.85/5.49  --instantiation_flag                    true
% 39.85/5.49  --inst_sos_flag                         false
% 39.85/5.49  --inst_sos_phase                        true
% 39.85/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.85/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.85/5.49  --inst_lit_sel_side                     num_symb
% 39.85/5.49  --inst_solver_per_active                1400
% 39.85/5.49  --inst_solver_calls_frac                1.
% 39.85/5.49  --inst_passive_queue_type               priority_queues
% 39.85/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.85/5.49  --inst_passive_queues_freq              [25;2]
% 39.85/5.49  --inst_dismatching                      true
% 39.85/5.49  --inst_eager_unprocessed_to_passive     true
% 39.85/5.49  --inst_prop_sim_given                   true
% 39.85/5.49  --inst_prop_sim_new                     false
% 39.85/5.49  --inst_subs_new                         false
% 39.85/5.49  --inst_eq_res_simp                      false
% 39.85/5.49  --inst_subs_given                       false
% 39.85/5.49  --inst_orphan_elimination               true
% 39.85/5.49  --inst_learning_loop_flag               true
% 39.85/5.49  --inst_learning_start                   3000
% 39.85/5.49  --inst_learning_factor                  2
% 39.85/5.49  --inst_start_prop_sim_after_learn       3
% 39.85/5.49  --inst_sel_renew                        solver
% 39.85/5.49  --inst_lit_activity_flag                true
% 39.85/5.49  --inst_restr_to_given                   false
% 39.85/5.49  --inst_activity_threshold               500
% 39.85/5.49  --inst_out_proof                        true
% 39.85/5.49  
% 39.85/5.49  ------ Resolution Options
% 39.85/5.49  
% 39.85/5.49  --resolution_flag                       true
% 39.85/5.49  --res_lit_sel                           adaptive
% 39.85/5.49  --res_lit_sel_side                      none
% 39.85/5.49  --res_ordering                          kbo
% 39.85/5.49  --res_to_prop_solver                    active
% 39.85/5.49  --res_prop_simpl_new                    false
% 39.85/5.49  --res_prop_simpl_given                  true
% 39.85/5.49  --res_passive_queue_type                priority_queues
% 39.85/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.85/5.49  --res_passive_queues_freq               [15;5]
% 39.85/5.49  --res_forward_subs                      full
% 39.85/5.49  --res_backward_subs                     full
% 39.85/5.49  --res_forward_subs_resolution           true
% 39.85/5.49  --res_backward_subs_resolution          true
% 39.85/5.49  --res_orphan_elimination                true
% 39.85/5.49  --res_time_limit                        2.
% 39.85/5.49  --res_out_proof                         true
% 39.85/5.49  
% 39.85/5.49  ------ Superposition Options
% 39.85/5.49  
% 39.85/5.49  --superposition_flag                    true
% 39.85/5.49  --sup_passive_queue_type                priority_queues
% 39.85/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.85/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.85/5.49  --demod_completeness_check              fast
% 39.85/5.49  --demod_use_ground                      true
% 39.85/5.49  --sup_to_prop_solver                    passive
% 39.85/5.49  --sup_prop_simpl_new                    true
% 39.85/5.49  --sup_prop_simpl_given                  true
% 39.85/5.49  --sup_fun_splitting                     false
% 39.85/5.49  --sup_smt_interval                      50000
% 39.85/5.49  
% 39.85/5.49  ------ Superposition Simplification Setup
% 39.85/5.49  
% 39.85/5.49  --sup_indices_passive                   []
% 39.85/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.85/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.85/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.85/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.85/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.85/5.49  --sup_full_bw                           [BwDemod]
% 39.85/5.49  --sup_immed_triv                        [TrivRules]
% 39.85/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.85/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.85/5.49  --sup_immed_bw_main                     []
% 39.85/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.85/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.85/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.85/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.85/5.49  
% 39.85/5.49  ------ Combination Options
% 39.85/5.49  
% 39.85/5.49  --comb_res_mult                         3
% 39.85/5.49  --comb_sup_mult                         2
% 39.85/5.49  --comb_inst_mult                        10
% 39.85/5.49  
% 39.85/5.49  ------ Debug Options
% 39.85/5.49  
% 39.85/5.49  --dbg_backtrace                         false
% 39.85/5.49  --dbg_dump_prop_clauses                 false
% 39.85/5.49  --dbg_dump_prop_clauses_file            -
% 39.85/5.49  --dbg_out_stat                          false
% 39.85/5.49  ------ Parsing...
% 39.85/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.85/5.49  
% 39.85/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.85/5.49  
% 39.85/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.85/5.49  
% 39.85/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.85/5.49  ------ Proving...
% 39.85/5.49  ------ Problem Properties 
% 39.85/5.49  
% 39.85/5.49  
% 39.85/5.49  clauses                                 15
% 39.85/5.49  conjectures                             3
% 39.85/5.49  EPR                                     6
% 39.85/5.49  Horn                                    15
% 39.85/5.49  unary                                   8
% 39.85/5.49  binary                                  2
% 39.85/5.49  lits                                    27
% 39.85/5.49  lits eq                                 3
% 39.85/5.49  fd_pure                                 0
% 39.85/5.49  fd_pseudo                               0
% 39.85/5.49  fd_cond                                 0
% 39.85/5.49  fd_pseudo_cond                          1
% 39.85/5.49  AC symbols                              0
% 39.85/5.49  
% 39.85/5.49  ------ Schedule dynamic 5 is on 
% 39.85/5.49  
% 39.85/5.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.85/5.49  
% 39.85/5.49  
% 39.85/5.49  ------ 
% 39.85/5.49  Current options:
% 39.85/5.49  ------ 
% 39.85/5.49  
% 39.85/5.49  ------ Input Options
% 39.85/5.49  
% 39.85/5.49  --out_options                           all
% 39.85/5.49  --tptp_safe_out                         true
% 39.85/5.49  --problem_path                          ""
% 39.85/5.49  --include_path                          ""
% 39.85/5.49  --clausifier                            res/vclausify_rel
% 39.85/5.49  --clausifier_options                    --mode clausify
% 39.85/5.49  --stdin                                 false
% 39.85/5.49  --stats_out                             all
% 39.85/5.49  
% 39.85/5.49  ------ General Options
% 39.85/5.49  
% 39.85/5.49  --fof                                   false
% 39.85/5.49  --time_out_real                         305.
% 39.85/5.49  --time_out_virtual                      -1.
% 39.85/5.49  --symbol_type_check                     false
% 39.85/5.49  --clausify_out                          false
% 39.85/5.49  --sig_cnt_out                           false
% 39.85/5.49  --trig_cnt_out                          false
% 39.85/5.49  --trig_cnt_out_tolerance                1.
% 39.85/5.49  --trig_cnt_out_sk_spl                   false
% 39.85/5.49  --abstr_cl_out                          false
% 39.85/5.49  
% 39.85/5.49  ------ Global Options
% 39.85/5.49  
% 39.85/5.49  --schedule                              default
% 39.85/5.49  --add_important_lit                     false
% 39.85/5.49  --prop_solver_per_cl                    1000
% 39.85/5.49  --min_unsat_core                        false
% 39.85/5.49  --soft_assumptions                      false
% 39.85/5.49  --soft_lemma_size                       3
% 39.85/5.49  --prop_impl_unit_size                   0
% 39.85/5.49  --prop_impl_unit                        []
% 39.85/5.49  --share_sel_clauses                     true
% 39.85/5.49  --reset_solvers                         false
% 39.85/5.49  --bc_imp_inh                            [conj_cone]
% 39.85/5.49  --conj_cone_tolerance                   3.
% 39.85/5.49  --extra_neg_conj                        none
% 39.85/5.49  --large_theory_mode                     true
% 39.85/5.49  --prolific_symb_bound                   200
% 39.85/5.49  --lt_threshold                          2000
% 39.85/5.49  --clause_weak_htbl                      true
% 39.85/5.49  --gc_record_bc_elim                     false
% 39.85/5.49  
% 39.85/5.49  ------ Preprocessing Options
% 39.85/5.49  
% 39.85/5.49  --preprocessing_flag                    true
% 39.85/5.49  --time_out_prep_mult                    0.1
% 39.85/5.49  --splitting_mode                        input
% 39.85/5.49  --splitting_grd                         true
% 39.85/5.49  --splitting_cvd                         false
% 39.85/5.49  --splitting_cvd_svl                     false
% 39.85/5.49  --splitting_nvd                         32
% 39.85/5.49  --sub_typing                            true
% 39.85/5.49  --prep_gs_sim                           true
% 39.85/5.49  --prep_unflatten                        true
% 39.85/5.49  --prep_res_sim                          true
% 39.85/5.49  --prep_upred                            true
% 39.85/5.49  --prep_sem_filter                       exhaustive
% 39.85/5.49  --prep_sem_filter_out                   false
% 39.85/5.49  --pred_elim                             true
% 39.85/5.49  --res_sim_input                         true
% 39.85/5.49  --eq_ax_congr_red                       true
% 39.85/5.49  --pure_diseq_elim                       true
% 39.85/5.49  --brand_transform                       false
% 39.85/5.49  --non_eq_to_eq                          false
% 39.85/5.49  --prep_def_merge                        true
% 39.85/5.49  --prep_def_merge_prop_impl              false
% 39.85/5.49  --prep_def_merge_mbd                    true
% 39.85/5.49  --prep_def_merge_tr_red                 false
% 39.85/5.49  --prep_def_merge_tr_cl                  false
% 39.85/5.49  --smt_preprocessing                     true
% 39.85/5.49  --smt_ac_axioms                         fast
% 39.85/5.49  --preprocessed_out                      false
% 39.85/5.49  --preprocessed_stats                    false
% 39.85/5.49  
% 39.85/5.49  ------ Abstraction refinement Options
% 39.85/5.49  
% 39.85/5.49  --abstr_ref                             []
% 39.85/5.49  --abstr_ref_prep                        false
% 39.85/5.49  --abstr_ref_until_sat                   false
% 39.85/5.49  --abstr_ref_sig_restrict                funpre
% 39.85/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.85/5.49  --abstr_ref_under                       []
% 39.85/5.49  
% 39.85/5.49  ------ SAT Options
% 39.85/5.49  
% 39.85/5.49  --sat_mode                              false
% 39.85/5.49  --sat_fm_restart_options                ""
% 39.85/5.49  --sat_gr_def                            false
% 39.85/5.49  --sat_epr_types                         true
% 39.85/5.49  --sat_non_cyclic_types                  false
% 39.85/5.49  --sat_finite_models                     false
% 39.85/5.49  --sat_fm_lemmas                         false
% 39.85/5.49  --sat_fm_prep                           false
% 39.85/5.49  --sat_fm_uc_incr                        true
% 39.85/5.49  --sat_out_model                         small
% 39.85/5.49  --sat_out_clauses                       false
% 39.85/5.49  
% 39.85/5.49  ------ QBF Options
% 39.85/5.49  
% 39.85/5.49  --qbf_mode                              false
% 39.85/5.49  --qbf_elim_univ                         false
% 39.85/5.49  --qbf_dom_inst                          none
% 39.85/5.49  --qbf_dom_pre_inst                      false
% 39.85/5.49  --qbf_sk_in                             false
% 39.85/5.49  --qbf_pred_elim                         true
% 39.85/5.49  --qbf_split                             512
% 39.85/5.49  
% 39.85/5.49  ------ BMC1 Options
% 39.85/5.49  
% 39.85/5.49  --bmc1_incremental                      false
% 39.85/5.49  --bmc1_axioms                           reachable_all
% 39.85/5.49  --bmc1_min_bound                        0
% 39.85/5.49  --bmc1_max_bound                        -1
% 39.85/5.49  --bmc1_max_bound_default                -1
% 39.85/5.49  --bmc1_symbol_reachability              true
% 39.85/5.49  --bmc1_property_lemmas                  false
% 39.85/5.49  --bmc1_k_induction                      false
% 39.85/5.49  --bmc1_non_equiv_states                 false
% 39.85/5.49  --bmc1_deadlock                         false
% 39.85/5.49  --bmc1_ucm                              false
% 39.85/5.49  --bmc1_add_unsat_core                   none
% 39.85/5.49  --bmc1_unsat_core_children              false
% 39.85/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.85/5.49  --bmc1_out_stat                         full
% 39.85/5.49  --bmc1_ground_init                      false
% 39.85/5.49  --bmc1_pre_inst_next_state              false
% 39.85/5.49  --bmc1_pre_inst_state                   false
% 39.85/5.49  --bmc1_pre_inst_reach_state             false
% 39.85/5.49  --bmc1_out_unsat_core                   false
% 39.85/5.49  --bmc1_aig_witness_out                  false
% 39.85/5.49  --bmc1_verbose                          false
% 39.85/5.49  --bmc1_dump_clauses_tptp                false
% 39.85/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.85/5.49  --bmc1_dump_file                        -
% 39.85/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.85/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.85/5.49  --bmc1_ucm_extend_mode                  1
% 39.85/5.49  --bmc1_ucm_init_mode                    2
% 39.85/5.49  --bmc1_ucm_cone_mode                    none
% 39.85/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.85/5.49  --bmc1_ucm_relax_model                  4
% 39.85/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.85/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.85/5.49  --bmc1_ucm_layered_model                none
% 39.85/5.49  --bmc1_ucm_max_lemma_size               10
% 39.85/5.49  
% 39.85/5.49  ------ AIG Options
% 39.85/5.49  
% 39.85/5.49  --aig_mode                              false
% 39.85/5.49  
% 39.85/5.49  ------ Instantiation Options
% 39.85/5.49  
% 39.85/5.49  --instantiation_flag                    true
% 39.85/5.49  --inst_sos_flag                         false
% 39.85/5.49  --inst_sos_phase                        true
% 39.85/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.85/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.85/5.49  --inst_lit_sel_side                     none
% 39.85/5.49  --inst_solver_per_active                1400
% 39.85/5.49  --inst_solver_calls_frac                1.
% 39.85/5.49  --inst_passive_queue_type               priority_queues
% 39.85/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.85/5.49  --inst_passive_queues_freq              [25;2]
% 39.85/5.49  --inst_dismatching                      true
% 39.85/5.49  --inst_eager_unprocessed_to_passive     true
% 39.85/5.49  --inst_prop_sim_given                   true
% 39.85/5.49  --inst_prop_sim_new                     false
% 39.85/5.49  --inst_subs_new                         false
% 39.85/5.49  --inst_eq_res_simp                      false
% 39.85/5.49  --inst_subs_given                       false
% 39.85/5.49  --inst_orphan_elimination               true
% 39.85/5.49  --inst_learning_loop_flag               true
% 39.85/5.49  --inst_learning_start                   3000
% 39.85/5.49  --inst_learning_factor                  2
% 39.85/5.49  --inst_start_prop_sim_after_learn       3
% 39.85/5.49  --inst_sel_renew                        solver
% 39.85/5.49  --inst_lit_activity_flag                true
% 39.85/5.49  --inst_restr_to_given                   false
% 39.85/5.49  --inst_activity_threshold               500
% 39.85/5.49  --inst_out_proof                        true
% 39.85/5.49  
% 39.85/5.49  ------ Resolution Options
% 39.85/5.49  
% 39.85/5.49  --resolution_flag                       false
% 39.85/5.49  --res_lit_sel                           adaptive
% 39.85/5.49  --res_lit_sel_side                      none
% 39.85/5.49  --res_ordering                          kbo
% 39.85/5.49  --res_to_prop_solver                    active
% 39.85/5.49  --res_prop_simpl_new                    false
% 39.85/5.49  --res_prop_simpl_given                  true
% 39.85/5.49  --res_passive_queue_type                priority_queues
% 39.85/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.85/5.49  --res_passive_queues_freq               [15;5]
% 39.85/5.49  --res_forward_subs                      full
% 39.85/5.49  --res_backward_subs                     full
% 39.85/5.49  --res_forward_subs_resolution           true
% 39.85/5.49  --res_backward_subs_resolution          true
% 39.85/5.49  --res_orphan_elimination                true
% 39.85/5.49  --res_time_limit                        2.
% 39.85/5.49  --res_out_proof                         true
% 39.85/5.49  
% 39.85/5.49  ------ Superposition Options
% 39.85/5.49  
% 39.85/5.49  --superposition_flag                    true
% 39.85/5.49  --sup_passive_queue_type                priority_queues
% 39.85/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.85/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.85/5.49  --demod_completeness_check              fast
% 39.85/5.49  --demod_use_ground                      true
% 39.85/5.49  --sup_to_prop_solver                    passive
% 39.85/5.49  --sup_prop_simpl_new                    true
% 39.85/5.49  --sup_prop_simpl_given                  true
% 39.85/5.49  --sup_fun_splitting                     false
% 39.85/5.49  --sup_smt_interval                      50000
% 39.85/5.49  
% 39.85/5.49  ------ Superposition Simplification Setup
% 39.85/5.49  
% 39.85/5.49  --sup_indices_passive                   []
% 39.85/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.85/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.85/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.85/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.85/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.85/5.49  --sup_full_bw                           [BwDemod]
% 39.85/5.49  --sup_immed_triv                        [TrivRules]
% 39.85/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.85/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.85/5.49  --sup_immed_bw_main                     []
% 39.85/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.85/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.85/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.85/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.85/5.49  
% 39.85/5.49  ------ Combination Options
% 39.85/5.49  
% 39.85/5.49  --comb_res_mult                         3
% 39.85/5.49  --comb_sup_mult                         2
% 39.85/5.49  --comb_inst_mult                        10
% 39.85/5.49  
% 39.85/5.49  ------ Debug Options
% 39.85/5.49  
% 39.85/5.49  --dbg_backtrace                         false
% 39.85/5.49  --dbg_dump_prop_clauses                 false
% 39.85/5.49  --dbg_dump_prop_clauses_file            -
% 39.85/5.49  --dbg_out_stat                          false
% 39.85/5.49  
% 39.85/5.49  
% 39.85/5.49  
% 39.85/5.49  
% 39.85/5.49  ------ Proving...
% 39.85/5.49  
% 39.85/5.49  
% 39.85/5.49  % SZS status Theorem for theBenchmark.p
% 39.85/5.49  
% 39.85/5.49   Resolution empty clause
% 39.85/5.49  
% 39.85/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.85/5.49  
% 39.85/5.49  fof(f1,axiom,(
% 39.85/5.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f24,plain,(
% 39.85/5.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.85/5.49    inference(nnf_transformation,[],[f1])).
% 39.85/5.49  
% 39.85/5.49  fof(f25,plain,(
% 39.85/5.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.85/5.49    inference(flattening,[],[f24])).
% 39.85/5.49  
% 39.85/5.49  fof(f31,plain,(
% 39.85/5.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 39.85/5.49    inference(cnf_transformation,[],[f25])).
% 39.85/5.49  
% 39.85/5.49  fof(f48,plain,(
% 39.85/5.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.85/5.49    inference(equality_resolution,[],[f31])).
% 39.85/5.49  
% 39.85/5.49  fof(f3,axiom,(
% 39.85/5.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f16,plain,(
% 39.85/5.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 39.85/5.49    inference(ennf_transformation,[],[f3])).
% 39.85/5.49  
% 39.85/5.49  fof(f34,plain,(
% 39.85/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 39.85/5.49    inference(cnf_transformation,[],[f16])).
% 39.85/5.49  
% 39.85/5.49  fof(f7,axiom,(
% 39.85/5.49    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f38,plain,(
% 39.85/5.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 39.85/5.49    inference(cnf_transformation,[],[f7])).
% 39.85/5.49  
% 39.85/5.49  fof(f13,conjecture,(
% 39.85/5.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f14,negated_conjecture,(
% 39.85/5.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 39.85/5.49    inference(negated_conjecture,[],[f13])).
% 39.85/5.49  
% 39.85/5.49  fof(f23,plain,(
% 39.85/5.49    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 39.85/5.49    inference(ennf_transformation,[],[f14])).
% 39.85/5.49  
% 39.85/5.49  fof(f28,plain,(
% 39.85/5.49    ( ! [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) & v1_relat_1(sK1))) )),
% 39.85/5.49    introduced(choice_axiom,[])).
% 39.85/5.49  
% 39.85/5.49  fof(f27,plain,(
% 39.85/5.49    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 39.85/5.49    introduced(choice_axiom,[])).
% 39.85/5.49  
% 39.85/5.49  fof(f29,plain,(
% 39.85/5.49    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 39.85/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28,f27])).
% 39.85/5.49  
% 39.85/5.49  fof(f46,plain,(
% 39.85/5.49    v1_relat_1(sK1)),
% 39.85/5.49    inference(cnf_transformation,[],[f29])).
% 39.85/5.49  
% 39.85/5.49  fof(f45,plain,(
% 39.85/5.49    v1_relat_1(sK0)),
% 39.85/5.49    inference(cnf_transformation,[],[f29])).
% 39.85/5.49  
% 39.85/5.49  fof(f4,axiom,(
% 39.85/5.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f35,plain,(
% 39.85/5.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 39.85/5.49    inference(cnf_transformation,[],[f4])).
% 39.85/5.49  
% 39.85/5.49  fof(f11,axiom,(
% 39.85/5.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f21,plain,(
% 39.85/5.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 39.85/5.49    inference(ennf_transformation,[],[f11])).
% 39.85/5.49  
% 39.85/5.49  fof(f43,plain,(
% 39.85/5.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 39.85/5.49    inference(cnf_transformation,[],[f21])).
% 39.85/5.49  
% 39.85/5.49  fof(f10,axiom,(
% 39.85/5.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f26,plain,(
% 39.85/5.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 39.85/5.49    inference(nnf_transformation,[],[f10])).
% 39.85/5.49  
% 39.85/5.49  fof(f42,plain,(
% 39.85/5.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 39.85/5.49    inference(cnf_transformation,[],[f26])).
% 39.85/5.49  
% 39.85/5.49  fof(f12,axiom,(
% 39.85/5.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f22,plain,(
% 39.85/5.49    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 39.85/5.49    inference(ennf_transformation,[],[f12])).
% 39.85/5.49  
% 39.85/5.49  fof(f44,plain,(
% 39.85/5.49    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 39.85/5.49    inference(cnf_transformation,[],[f22])).
% 39.85/5.49  
% 39.85/5.49  fof(f8,axiom,(
% 39.85/5.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f39,plain,(
% 39.85/5.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 39.85/5.49    inference(cnf_transformation,[],[f8])).
% 39.85/5.49  
% 39.85/5.49  fof(f2,axiom,(
% 39.85/5.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f15,plain,(
% 39.85/5.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 39.85/5.49    inference(ennf_transformation,[],[f2])).
% 39.85/5.49  
% 39.85/5.49  fof(f33,plain,(
% 39.85/5.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 39.85/5.49    inference(cnf_transformation,[],[f15])).
% 39.85/5.49  
% 39.85/5.49  fof(f5,axiom,(
% 39.85/5.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 39.85/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.85/5.49  
% 39.85/5.49  fof(f17,plain,(
% 39.85/5.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 39.85/5.49    inference(ennf_transformation,[],[f5])).
% 39.85/5.49  
% 39.85/5.49  fof(f18,plain,(
% 39.85/5.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 39.85/5.49    inference(flattening,[],[f17])).
% 39.85/5.49  
% 39.85/5.49  fof(f36,plain,(
% 39.85/5.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 39.85/5.49    inference(cnf_transformation,[],[f18])).
% 39.85/5.49  
% 39.85/5.49  fof(f47,plain,(
% 39.85/5.49    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 39.85/5.49    inference(cnf_transformation,[],[f29])).
% 39.85/5.49  
% 39.85/5.49  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f48]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_597,plain,
% 39.85/5.49      ( r1_tarski(X0,X0) = iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_4,plain,
% 39.85/5.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 39.85/5.49      inference(cnf_transformation,[],[f34]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_595,plain,
% 39.85/5.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_949,plain,
% 39.85/5.49      ( k2_xboole_0(X0,X0) = X0 ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_597,c_595]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_8,plain,
% 39.85/5.49      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
% 39.85/5.49      inference(cnf_transformation,[],[f38]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_591,plain,
% 39.85/5.49      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_1451,plain,
% 39.85/5.49      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_949,c_591]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_1452,plain,
% 39.85/5.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 39.85/5.49      inference(demodulation,[status(thm)],[c_1451,c_949]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_1632,plain,
% 39.85/5.49      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_1452,c_595]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_16,negated_conjecture,
% 39.85/5.49      ( v1_relat_1(sK1) ),
% 39.85/5.49      inference(cnf_transformation,[],[f46]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_586,plain,
% 39.85/5.49      ( v1_relat_1(sK1) = iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_17,negated_conjecture,
% 39.85/5.49      ( v1_relat_1(sK0) ),
% 39.85/5.49      inference(cnf_transformation,[],[f45]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_585,plain,
% 39.85/5.49      ( v1_relat_1(sK0) = iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_5,plain,
% 39.85/5.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 39.85/5.49      inference(cnf_transformation,[],[f35]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_594,plain,
% 39.85/5.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_13,plain,
% 39.85/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 39.85/5.49      inference(cnf_transformation,[],[f43]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_11,plain,
% 39.85/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.85/5.49      inference(cnf_transformation,[],[f42]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_139,plain,
% 39.85/5.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 39.85/5.49      inference(prop_impl,[status(thm)],[c_11]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_140,plain,
% 39.85/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.85/5.49      inference(renaming,[status(thm)],[c_139]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_167,plain,
% 39.85/5.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 39.85/5.49      inference(bin_hyper_res,[status(thm)],[c_13,c_140]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_584,plain,
% 39.85/5.49      ( r1_tarski(X0,X1) != iProver_top
% 39.85/5.49      | v1_relat_1(X1) != iProver_top
% 39.85/5.49      | v1_relat_1(X0) = iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_1064,plain,
% 39.85/5.49      ( v1_relat_1(X0) != iProver_top
% 39.85/5.49      | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_594,c_584]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_14,plain,
% 39.85/5.49      ( ~ v1_relat_1(X0)
% 39.85/5.49      | ~ v1_relat_1(X1)
% 39.85/5.49      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
% 39.85/5.49      inference(cnf_transformation,[],[f44]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_588,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
% 39.85/5.49      | v1_relat_1(X0) != iProver_top
% 39.85/5.49      | v1_relat_1(X1) != iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_3364,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(k3_xboole_0(X0,X1)),k1_relat_1(X2)) = k1_relat_1(k2_xboole_0(k3_xboole_0(X0,X1),X2))
% 39.85/5.49      | v1_relat_1(X0) != iProver_top
% 39.85/5.49      | v1_relat_1(X2) != iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_1064,c_588]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_122384,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),X1))
% 39.85/5.49      | v1_relat_1(X1) != iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_585,c_3364]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_125636,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1)) ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_586,c_122384]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_9,plain,
% 39.85/5.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 39.85/5.49      inference(cnf_transformation,[],[f39]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_590,plain,
% 39.85/5.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_952,plain,
% 39.85/5.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_590,c_595]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_125709,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1))) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK1)) ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_125636,c_952]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_125817,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1))) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1)) ),
% 39.85/5.49      inference(light_normalisation,[status(thm)],[c_125709,c_125636]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_141951,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)) ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_1632,c_125817]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_142065,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
% 39.85/5.49      inference(demodulation,[status(thm)],[c_141951,c_1632,c_125636]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_3,plain,
% 39.85/5.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 39.85/5.49      inference(cnf_transformation,[],[f33]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_596,plain,
% 39.85/5.49      ( r1_tarski(X0,X1) = iProver_top
% 39.85/5.49      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_142346,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X0) = iProver_top
% 39.85/5.49      | r1_tarski(k1_relat_1(sK1),X0) != iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_142065,c_596]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_6,plain,
% 39.85/5.49      ( ~ r1_tarski(X0,X1)
% 39.85/5.49      | ~ r1_tarski(X0,X2)
% 39.85/5.49      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 39.85/5.49      inference(cnf_transformation,[],[f36]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_593,plain,
% 39.85/5.49      ( r1_tarski(X0,X1) != iProver_top
% 39.85/5.49      | r1_tarski(X0,X2) != iProver_top
% 39.85/5.49      | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_15,negated_conjecture,
% 39.85/5.49      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
% 39.85/5.49      inference(cnf_transformation,[],[f47]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_587,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_2112,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) != iProver_top
% 39.85/5.49      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_593,c_587]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_175100,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top
% 39.85/5.49      | r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) != iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_142346,c_2112]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_20,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) != iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_694,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
% 39.85/5.49      | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
% 39.85/5.49      | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
% 39.85/5.49      inference(instantiation,[status(thm)],[c_6]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_695,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) = iProver_top
% 39.85/5.49      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) != iProver_top
% 39.85/5.49      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top ),
% 39.85/5.49      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_125710,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1))) = iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_125636,c_590]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_128853,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) = iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_1632,c_125710]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_175684,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) != iProver_top ),
% 39.85/5.49      inference(global_propositional_subsumption,
% 39.85/5.49                [status(thm)],
% 39.85/5.49                [c_175100,c_20,c_695,c_128853]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_125637,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK0)) ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_585,c_122384]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_950,plain,
% 39.85/5.49      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_594,c_595]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_125667,plain,
% 39.85/5.49      ( k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK0)) = k1_relat_1(sK0) ),
% 39.85/5.49      inference(demodulation,[status(thm)],[c_125637,c_950]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_126480,plain,
% 39.85/5.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK0)) = iProver_top ),
% 39.85/5.49      inference(superposition,[status(thm)],[c_125667,c_590]) ).
% 39.85/5.49  
% 39.85/5.49  cnf(c_175689,plain,
% 39.85/5.49      ( $false ),
% 39.85/5.49      inference(forward_subsumption_resolution,
% 39.85/5.49                [status(thm)],
% 39.85/5.49                [c_175684,c_126480]) ).
% 39.85/5.49  
% 39.85/5.49  
% 39.85/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.85/5.49  
% 39.85/5.49  ------                               Statistics
% 39.85/5.49  
% 39.85/5.49  ------ General
% 39.85/5.49  
% 39.85/5.49  abstr_ref_over_cycles:                  0
% 39.85/5.49  abstr_ref_under_cycles:                 0
% 39.85/5.49  gc_basic_clause_elim:                   0
% 39.85/5.49  forced_gc_time:                         0
% 39.85/5.49  parsing_time:                           0.009
% 39.85/5.49  unif_index_cands_time:                  0.
% 39.85/5.49  unif_index_add_time:                    0.
% 39.85/5.49  orderings_time:                         0.
% 39.85/5.49  out_proof_time:                         0.027
% 39.85/5.49  total_time:                             4.904
% 39.85/5.49  num_of_symbols:                         41
% 39.85/5.49  num_of_terms:                           201784
% 39.85/5.49  
% 39.85/5.49  ------ Preprocessing
% 39.85/5.49  
% 39.85/5.49  num_of_splits:                          0
% 39.85/5.49  num_of_split_atoms:                     0
% 39.85/5.49  num_of_reused_defs:                     0
% 39.85/5.49  num_eq_ax_congr_red:                    2
% 39.85/5.49  num_of_sem_filtered_clauses:            1
% 39.85/5.49  num_of_subtypes:                        0
% 39.85/5.49  monotx_restored_types:                  0
% 39.85/5.49  sat_num_of_epr_types:                   0
% 39.85/5.49  sat_num_of_non_cyclic_types:            0
% 39.85/5.49  sat_guarded_non_collapsed_types:        0
% 39.85/5.49  num_pure_diseq_elim:                    0
% 39.85/5.49  simp_replaced_by:                       0
% 39.85/5.49  res_preprocessed:                       77
% 39.85/5.49  prep_upred:                             0
% 39.85/5.49  prep_unflattend:                        0
% 39.85/5.49  smt_new_axioms:                         0
% 39.85/5.49  pred_elim_cands:                        2
% 39.85/5.49  pred_elim:                              1
% 39.85/5.49  pred_elim_cl:                           2
% 39.85/5.49  pred_elim_cycles:                       3
% 39.85/5.49  merged_defs:                            2
% 39.85/5.49  merged_defs_ncl:                        0
% 39.85/5.49  bin_hyper_res:                          3
% 39.85/5.49  prep_cycles:                            4
% 39.85/5.49  pred_elim_time:                         0.
% 39.85/5.49  splitting_time:                         0.
% 39.85/5.49  sem_filter_time:                        0.
% 39.85/5.49  monotx_time:                            0.001
% 39.85/5.49  subtype_inf_time:                       0.
% 39.85/5.49  
% 39.85/5.49  ------ Problem properties
% 39.85/5.49  
% 39.85/5.49  clauses:                                15
% 39.85/5.49  conjectures:                            3
% 39.85/5.49  epr:                                    6
% 39.85/5.49  horn:                                   15
% 39.85/5.49  ground:                                 3
% 39.85/5.49  unary:                                  8
% 39.85/5.49  binary:                                 2
% 39.85/5.49  lits:                                   27
% 39.85/5.49  lits_eq:                                3
% 39.85/5.49  fd_pure:                                0
% 39.85/5.49  fd_pseudo:                              0
% 39.85/5.49  fd_cond:                                0
% 39.85/5.49  fd_pseudo_cond:                         1
% 39.85/5.49  ac_symbols:                             0
% 39.85/5.49  
% 39.85/5.49  ------ Propositional Solver
% 39.85/5.49  
% 39.85/5.49  prop_solver_calls:                      74
% 39.85/5.49  prop_fast_solver_calls:                 1018
% 39.85/5.49  smt_solver_calls:                       0
% 39.85/5.49  smt_fast_solver_calls:                  0
% 39.85/5.49  prop_num_of_clauses:                    72825
% 39.85/5.49  prop_preprocess_simplified:             106770
% 39.85/5.49  prop_fo_subsumed:                       5
% 39.85/5.49  prop_solver_time:                       0.
% 39.85/5.49  smt_solver_time:                        0.
% 39.85/5.49  smt_fast_solver_time:                   0.
% 39.85/5.49  prop_fast_solver_time:                  0.
% 39.85/5.49  prop_unsat_core_time:                   0.
% 39.85/5.49  
% 39.85/5.49  ------ QBF
% 39.85/5.49  
% 39.85/5.49  qbf_q_res:                              0
% 39.85/5.49  qbf_num_tautologies:                    0
% 39.85/5.49  qbf_prep_cycles:                        0
% 39.85/5.49  
% 39.85/5.49  ------ BMC1
% 39.85/5.49  
% 39.85/5.49  bmc1_current_bound:                     -1
% 39.85/5.49  bmc1_last_solved_bound:                 -1
% 39.85/5.49  bmc1_unsat_core_size:                   -1
% 39.85/5.49  bmc1_unsat_core_parents_size:           -1
% 39.85/5.49  bmc1_merge_next_fun:                    0
% 39.85/5.49  bmc1_unsat_core_clauses_time:           0.
% 39.85/5.49  
% 39.85/5.49  ------ Instantiation
% 39.85/5.49  
% 39.85/5.49  inst_num_of_clauses:                    14343
% 39.85/5.49  inst_num_in_passive:                    12438
% 39.85/5.49  inst_num_in_active:                     1842
% 39.85/5.49  inst_num_in_unprocessed:                66
% 39.85/5.49  inst_num_of_loops:                      2390
% 39.85/5.49  inst_num_of_learning_restarts:          0
% 39.85/5.49  inst_num_moves_active_passive:          542
% 39.85/5.49  inst_lit_activity:                      0
% 39.85/5.49  inst_lit_activity_moves:                3
% 39.85/5.49  inst_num_tautologies:                   0
% 39.85/5.49  inst_num_prop_implied:                  0
% 39.85/5.49  inst_num_existing_simplified:           0
% 39.85/5.49  inst_num_eq_res_simplified:             0
% 39.85/5.49  inst_num_child_elim:                    0
% 39.85/5.49  inst_num_of_dismatching_blockings:      20222
% 39.85/5.49  inst_num_of_non_proper_insts:           15760
% 39.85/5.49  inst_num_of_duplicates:                 0
% 39.85/5.49  inst_inst_num_from_inst_to_res:         0
% 39.85/5.49  inst_dismatching_checking_time:         0.
% 39.85/5.49  
% 39.85/5.49  ------ Resolution
% 39.85/5.49  
% 39.85/5.49  res_num_of_clauses:                     0
% 39.85/5.49  res_num_in_passive:                     0
% 39.85/5.49  res_num_in_active:                      0
% 39.85/5.49  res_num_of_loops:                       81
% 39.85/5.49  res_forward_subset_subsumed:            2056
% 39.85/5.49  res_backward_subset_subsumed:           10
% 39.85/5.49  res_forward_subsumed:                   0
% 39.85/5.49  res_backward_subsumed:                  0
% 39.85/5.49  res_forward_subsumption_resolution:     0
% 39.85/5.49  res_backward_subsumption_resolution:    0
% 39.85/5.49  res_clause_to_clause_subsumption:       59745
% 39.85/5.49  res_orphan_elimination:                 0
% 39.85/5.49  res_tautology_del:                      237
% 39.85/5.49  res_num_eq_res_simplified:              0
% 39.85/5.49  res_num_sel_changes:                    0
% 39.85/5.49  res_moves_from_active_to_pass:          0
% 39.85/5.49  
% 39.85/5.49  ------ Superposition
% 39.85/5.49  
% 39.85/5.49  sup_time_total:                         0.
% 39.85/5.49  sup_time_generating:                    0.
% 39.85/5.49  sup_time_sim_full:                      0.
% 39.85/5.49  sup_time_sim_immed:                     0.
% 39.85/5.49  
% 39.85/5.49  sup_num_of_clauses:                     7331
% 39.85/5.49  sup_num_in_active:                      455
% 39.85/5.49  sup_num_in_passive:                     6876
% 39.85/5.49  sup_num_of_loops:                       477
% 39.85/5.49  sup_fw_superposition:                   6424
% 39.85/5.49  sup_bw_superposition:                   6918
% 39.85/5.49  sup_immediate_simplified:               3465
% 39.85/5.49  sup_given_eliminated:                   15
% 39.85/5.49  comparisons_done:                       0
% 39.85/5.49  comparisons_avoided:                    0
% 39.85/5.49  
% 39.85/5.49  ------ Simplifications
% 39.85/5.49  
% 39.85/5.49  
% 39.85/5.49  sim_fw_subset_subsumed:                 43
% 39.85/5.49  sim_bw_subset_subsumed:                 31
% 39.85/5.49  sim_fw_subsumed:                        471
% 39.85/5.49  sim_bw_subsumed:                        22
% 39.85/5.49  sim_fw_subsumption_res:                 59
% 39.85/5.49  sim_bw_subsumption_res:                 0
% 39.85/5.49  sim_tautology_del:                      186
% 39.85/5.49  sim_eq_tautology_del:                   150
% 39.85/5.49  sim_eq_res_simp:                        0
% 39.85/5.49  sim_fw_demodulated:                     1580
% 39.85/5.49  sim_bw_demodulated:                     36
% 39.85/5.49  sim_light_normalised:                   1541
% 39.85/5.49  sim_joinable_taut:                      0
% 39.85/5.49  sim_joinable_simp:                      0
% 39.85/5.49  sim_ac_normalised:                      0
% 39.85/5.49  sim_smt_subsumption:                    0
% 39.85/5.49  
%------------------------------------------------------------------------------

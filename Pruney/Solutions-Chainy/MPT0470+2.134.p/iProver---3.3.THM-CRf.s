%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:18 EST 2020

% Result     : Theorem 19.93s
% Output     : CNFRefutation 19.93s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 216 expanded)
%              Number of clauses        :   63 (  90 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  295 ( 543 expanded)
%              Number of equality atoms :  177 ( 366 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f131,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f83])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f168,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f122])).

fof(f21,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f141,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f65,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f96,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) )
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) )
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f65,f96])).

fof(f158,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f97])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f140,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f147,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f35,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f156,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f157,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f34,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f63])).

fof(f94,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f64,f94])).

fof(f155,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f169,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f121])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f159,plain,
    ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_33,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_93754,plain,
    ( k2_xboole_0(k1_tarski(sK6(k5_relat_1(k1_xboole_0,sK8))),k1_relat_1(k5_relat_1(k1_xboole_0,sK8))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f168])).

cnf(c_43,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_2658,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_3351,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_2658])).

cnf(c_61,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_2643,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_42,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2659,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_49,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f147])).

cnf(c_2652,plain,
    ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_7974,plain,
    ( k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1)))) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2659,c_2652])).

cnf(c_83785,plain,
    ( k3_xboole_0(k5_relat_1(sK8,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK8,X0)),k2_relat_1(k5_relat_1(sK8,X0)))) = k5_relat_1(sK8,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2643,c_7974])).

cnf(c_84300,plain,
    ( k3_xboole_0(k5_relat_1(sK8,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK8,k1_xboole_0)),k2_relat_1(k5_relat_1(sK8,k1_xboole_0)))) = k5_relat_1(sK8,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3351,c_83785])).

cnf(c_59,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f156])).

cnf(c_54,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_2647,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_4680,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_59,c_2647])).

cnf(c_58,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f157])).

cnf(c_4694,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4680,c_58])).

cnf(c_16436,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4694,c_3351])).

cnf(c_16437,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16436])).

cnf(c_14,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2675,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6330,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_2675])).

cnf(c_16443,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16437,c_6330])).

cnf(c_16449,plain,
    ( k2_relat_1(k5_relat_1(sK8,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2643,c_16443])).

cnf(c_84423,plain,
    ( k3_xboole_0(k5_relat_1(sK8,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(sK8,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_84300,c_16449])).

cnf(c_13,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_84424,plain,
    ( k5_relat_1(sK8,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_84423,c_13,c_22])).

cnf(c_1684,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_81846,plain,
    ( X0 != X1
    | X0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK8))
    | k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) != X1 ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_81847,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK8))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_81846])).

cnf(c_3223,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != X2
    | k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_71382,plain,
    ( k2_xboole_0(k1_tarski(sK6(k5_relat_1(k1_xboole_0,sK8))),k1_relat_1(k5_relat_1(k1_xboole_0,sK8))) != k1_relat_1(k5_relat_1(k1_xboole_0,sK8))
    | k2_xboole_0(k1_tarski(sK6(k5_relat_1(k1_xboole_0,sK8))),k1_relat_1(k5_relat_1(k1_xboole_0,sK8))) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
    inference(instantiation,[status(thm)],[c_3223])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_23750,plain,
    ( ~ r2_hidden(sK6(k5_relat_1(k1_xboole_0,sK8)),k1_relat_1(k5_relat_1(k1_xboole_0,sK8)))
    | k2_xboole_0(k1_tarski(sK6(k5_relat_1(k1_xboole_0,sK8))),k1_relat_1(k5_relat_1(k1_xboole_0,sK8))) = k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_53,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_2648,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_5651,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_58,c_2648])).

cnf(c_5665,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5651,c_59])).

cnf(c_16503,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5665,c_3351])).

cnf(c_16504,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16503])).

cnf(c_16510,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16504,c_6330])).

cnf(c_16516,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2643,c_16510])).

cnf(c_48,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_3359,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK8)))
    | ~ r2_hidden(k4_tarski(X0,X2),k5_relat_1(X1,sK8))
    | ~ v1_relat_1(k5_relat_1(X1,sK8)) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_4416,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k5_relat_1(k1_xboole_0,sK8)),sK7(k5_relat_1(k1_xboole_0,sK8))),k5_relat_1(k1_xboole_0,sK8))
    | r2_hidden(sK6(k5_relat_1(k1_xboole_0,sK8)),k1_relat_1(k5_relat_1(k1_xboole_0,sK8)))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
    inference(instantiation,[status(thm)],[c_3359])).

cnf(c_57,plain,
    ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f155])).

cnf(c_3454,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(k1_xboole_0,sK8)),sK7(k5_relat_1(k1_xboole_0,sK8))),k5_relat_1(k1_xboole_0,sK8))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK8))
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8) ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_3353,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3351])).

cnf(c_3226,plain,
    ( k5_relat_1(sK8,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_3227,plain,
    ( k5_relat_1(sK8,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3226])).

cnf(c_3090,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k5_relat_1(X0,sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_3092,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3090])).

cnf(c_23,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f169])).

cnf(c_141,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_24,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_140,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_60,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
    inference(cnf_transformation,[],[f159])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93754,c_84424,c_81847,c_71382,c_23750,c_16516,c_4416,c_3454,c_3353,c_3227,c_3092,c_141,c_140,c_60,c_61])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.93/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.93/2.99  
% 19.93/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.93/2.99  
% 19.93/2.99  ------  iProver source info
% 19.93/2.99  
% 19.93/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.93/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.93/2.99  git: non_committed_changes: false
% 19.93/2.99  git: last_make_outside_of_git: false
% 19.93/2.99  
% 19.93/2.99  ------ 
% 19.93/2.99  
% 19.93/2.99  ------ Input Options
% 19.93/2.99  
% 19.93/2.99  --out_options                           all
% 19.93/2.99  --tptp_safe_out                         true
% 19.93/2.99  --problem_path                          ""
% 19.93/2.99  --include_path                          ""
% 19.93/2.99  --clausifier                            res/vclausify_rel
% 19.93/2.99  --clausifier_options                    --mode clausify
% 19.93/2.99  --stdin                                 false
% 19.93/2.99  --stats_out                             all
% 19.93/2.99  
% 19.93/2.99  ------ General Options
% 19.93/2.99  
% 19.93/2.99  --fof                                   false
% 19.93/2.99  --time_out_real                         305.
% 19.93/2.99  --time_out_virtual                      -1.
% 19.93/2.99  --symbol_type_check                     false
% 19.93/2.99  --clausify_out                          false
% 19.93/2.99  --sig_cnt_out                           false
% 19.93/2.99  --trig_cnt_out                          false
% 19.93/2.99  --trig_cnt_out_tolerance                1.
% 19.93/2.99  --trig_cnt_out_sk_spl                   false
% 19.93/2.99  --abstr_cl_out                          false
% 19.93/2.99  
% 19.93/2.99  ------ Global Options
% 19.93/2.99  
% 19.93/2.99  --schedule                              default
% 19.93/2.99  --add_important_lit                     false
% 19.93/2.99  --prop_solver_per_cl                    1000
% 19.93/2.99  --min_unsat_core                        false
% 19.93/2.99  --soft_assumptions                      false
% 19.93/2.99  --soft_lemma_size                       3
% 19.93/2.99  --prop_impl_unit_size                   0
% 19.93/2.99  --prop_impl_unit                        []
% 19.93/2.99  --share_sel_clauses                     true
% 19.93/2.99  --reset_solvers                         false
% 19.93/2.99  --bc_imp_inh                            [conj_cone]
% 19.93/2.99  --conj_cone_tolerance                   3.
% 19.93/2.99  --extra_neg_conj                        none
% 19.93/2.99  --large_theory_mode                     true
% 19.93/2.99  --prolific_symb_bound                   200
% 19.93/2.99  --lt_threshold                          2000
% 19.93/2.99  --clause_weak_htbl                      true
% 19.93/2.99  --gc_record_bc_elim                     false
% 19.93/2.99  
% 19.93/2.99  ------ Preprocessing Options
% 19.93/2.99  
% 19.93/2.99  --preprocessing_flag                    true
% 19.93/2.99  --time_out_prep_mult                    0.1
% 19.93/2.99  --splitting_mode                        input
% 19.93/2.99  --splitting_grd                         true
% 19.93/2.99  --splitting_cvd                         false
% 19.93/2.99  --splitting_cvd_svl                     false
% 19.93/2.99  --splitting_nvd                         32
% 19.93/2.99  --sub_typing                            true
% 19.93/2.99  --prep_gs_sim                           true
% 19.93/2.99  --prep_unflatten                        true
% 19.93/2.99  --prep_res_sim                          true
% 19.93/2.99  --prep_upred                            true
% 19.93/2.99  --prep_sem_filter                       exhaustive
% 19.93/2.99  --prep_sem_filter_out                   false
% 19.93/2.99  --pred_elim                             true
% 19.93/2.99  --res_sim_input                         true
% 19.93/2.99  --eq_ax_congr_red                       true
% 19.93/2.99  --pure_diseq_elim                       true
% 19.93/2.99  --brand_transform                       false
% 19.93/2.99  --non_eq_to_eq                          false
% 19.93/2.99  --prep_def_merge                        true
% 19.93/2.99  --prep_def_merge_prop_impl              false
% 19.93/2.99  --prep_def_merge_mbd                    true
% 19.93/2.99  --prep_def_merge_tr_red                 false
% 19.93/2.99  --prep_def_merge_tr_cl                  false
% 19.93/2.99  --smt_preprocessing                     true
% 19.93/2.99  --smt_ac_axioms                         fast
% 19.93/2.99  --preprocessed_out                      false
% 19.93/2.99  --preprocessed_stats                    false
% 19.93/2.99  
% 19.93/2.99  ------ Abstraction refinement Options
% 19.93/2.99  
% 19.93/2.99  --abstr_ref                             []
% 19.93/2.99  --abstr_ref_prep                        false
% 19.93/2.99  --abstr_ref_until_sat                   false
% 19.93/2.99  --abstr_ref_sig_restrict                funpre
% 19.93/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.93/2.99  --abstr_ref_under                       []
% 19.93/2.99  
% 19.93/2.99  ------ SAT Options
% 19.93/2.99  
% 19.93/2.99  --sat_mode                              false
% 19.93/2.99  --sat_fm_restart_options                ""
% 19.93/2.99  --sat_gr_def                            false
% 19.93/2.99  --sat_epr_types                         true
% 19.93/2.99  --sat_non_cyclic_types                  false
% 19.93/2.99  --sat_finite_models                     false
% 19.93/2.99  --sat_fm_lemmas                         false
% 19.93/2.99  --sat_fm_prep                           false
% 19.93/2.99  --sat_fm_uc_incr                        true
% 19.93/2.99  --sat_out_model                         small
% 19.93/2.99  --sat_out_clauses                       false
% 19.93/2.99  
% 19.93/2.99  ------ QBF Options
% 19.93/2.99  
% 19.93/2.99  --qbf_mode                              false
% 19.93/2.99  --qbf_elim_univ                         false
% 19.93/2.99  --qbf_dom_inst                          none
% 19.93/2.99  --qbf_dom_pre_inst                      false
% 19.93/2.99  --qbf_sk_in                             false
% 19.93/2.99  --qbf_pred_elim                         true
% 19.93/2.99  --qbf_split                             512
% 19.93/2.99  
% 19.93/2.99  ------ BMC1 Options
% 19.93/2.99  
% 19.93/2.99  --bmc1_incremental                      false
% 19.93/2.99  --bmc1_axioms                           reachable_all
% 19.93/2.99  --bmc1_min_bound                        0
% 19.93/2.99  --bmc1_max_bound                        -1
% 19.93/2.99  --bmc1_max_bound_default                -1
% 19.93/2.99  --bmc1_symbol_reachability              true
% 19.93/2.99  --bmc1_property_lemmas                  false
% 19.93/2.99  --bmc1_k_induction                      false
% 19.93/2.99  --bmc1_non_equiv_states                 false
% 19.93/2.99  --bmc1_deadlock                         false
% 19.93/2.99  --bmc1_ucm                              false
% 19.93/2.99  --bmc1_add_unsat_core                   none
% 19.93/2.99  --bmc1_unsat_core_children              false
% 19.93/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.93/2.99  --bmc1_out_stat                         full
% 19.93/2.99  --bmc1_ground_init                      false
% 19.93/2.99  --bmc1_pre_inst_next_state              false
% 19.93/2.99  --bmc1_pre_inst_state                   false
% 19.93/2.99  --bmc1_pre_inst_reach_state             false
% 19.93/2.99  --bmc1_out_unsat_core                   false
% 19.93/2.99  --bmc1_aig_witness_out                  false
% 19.93/2.99  --bmc1_verbose                          false
% 19.93/2.99  --bmc1_dump_clauses_tptp                false
% 19.93/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.93/2.99  --bmc1_dump_file                        -
% 19.93/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.93/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.93/2.99  --bmc1_ucm_extend_mode                  1
% 19.93/2.99  --bmc1_ucm_init_mode                    2
% 19.93/2.99  --bmc1_ucm_cone_mode                    none
% 19.93/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.93/2.99  --bmc1_ucm_relax_model                  4
% 19.93/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.93/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.93/2.99  --bmc1_ucm_layered_model                none
% 19.93/2.99  --bmc1_ucm_max_lemma_size               10
% 19.93/2.99  
% 19.93/2.99  ------ AIG Options
% 19.93/2.99  
% 19.93/2.99  --aig_mode                              false
% 19.93/2.99  
% 19.93/2.99  ------ Instantiation Options
% 19.93/2.99  
% 19.93/2.99  --instantiation_flag                    true
% 19.93/2.99  --inst_sos_flag                         false
% 19.93/2.99  --inst_sos_phase                        true
% 19.93/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.93/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.93/2.99  --inst_lit_sel_side                     num_symb
% 19.93/2.99  --inst_solver_per_active                1400
% 19.93/2.99  --inst_solver_calls_frac                1.
% 19.93/2.99  --inst_passive_queue_type               priority_queues
% 19.93/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.93/2.99  --inst_passive_queues_freq              [25;2]
% 19.93/2.99  --inst_dismatching                      true
% 19.93/2.99  --inst_eager_unprocessed_to_passive     true
% 19.93/2.99  --inst_prop_sim_given                   true
% 19.93/2.99  --inst_prop_sim_new                     false
% 19.93/2.99  --inst_subs_new                         false
% 19.93/2.99  --inst_eq_res_simp                      false
% 19.93/2.99  --inst_subs_given                       false
% 19.93/2.99  --inst_orphan_elimination               true
% 19.93/2.99  --inst_learning_loop_flag               true
% 19.93/2.99  --inst_learning_start                   3000
% 19.93/2.99  --inst_learning_factor                  2
% 19.93/2.99  --inst_start_prop_sim_after_learn       3
% 19.93/2.99  --inst_sel_renew                        solver
% 19.93/2.99  --inst_lit_activity_flag                true
% 19.93/2.99  --inst_restr_to_given                   false
% 19.93/2.99  --inst_activity_threshold               500
% 19.93/2.99  --inst_out_proof                        true
% 19.93/2.99  
% 19.93/2.99  ------ Resolution Options
% 19.93/2.99  
% 19.93/2.99  --resolution_flag                       true
% 19.93/2.99  --res_lit_sel                           adaptive
% 19.93/2.99  --res_lit_sel_side                      none
% 19.93/2.99  --res_ordering                          kbo
% 19.93/2.99  --res_to_prop_solver                    active
% 19.93/2.99  --res_prop_simpl_new                    false
% 19.93/2.99  --res_prop_simpl_given                  true
% 19.93/2.99  --res_passive_queue_type                priority_queues
% 19.93/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.93/2.99  --res_passive_queues_freq               [15;5]
% 19.93/2.99  --res_forward_subs                      full
% 19.93/2.99  --res_backward_subs                     full
% 19.93/2.99  --res_forward_subs_resolution           true
% 19.93/2.99  --res_backward_subs_resolution          true
% 19.93/2.99  --res_orphan_elimination                true
% 19.93/2.99  --res_time_limit                        2.
% 19.93/2.99  --res_out_proof                         true
% 19.93/2.99  
% 19.93/2.99  ------ Superposition Options
% 19.93/2.99  
% 19.93/2.99  --superposition_flag                    true
% 19.93/2.99  --sup_passive_queue_type                priority_queues
% 19.93/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.93/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.93/2.99  --demod_completeness_check              fast
% 19.93/2.99  --demod_use_ground                      true
% 19.93/2.99  --sup_to_prop_solver                    passive
% 19.93/2.99  --sup_prop_simpl_new                    true
% 19.93/2.99  --sup_prop_simpl_given                  true
% 19.93/2.99  --sup_fun_splitting                     false
% 19.93/2.99  --sup_smt_interval                      50000
% 19.93/2.99  
% 19.93/2.99  ------ Superposition Simplification Setup
% 19.93/2.99  
% 19.93/2.99  --sup_indices_passive                   []
% 19.93/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.93/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.93/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.93/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.93/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.93/2.99  --sup_full_bw                           [BwDemod]
% 19.93/2.99  --sup_immed_triv                        [TrivRules]
% 19.93/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.93/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.93/2.99  --sup_immed_bw_main                     []
% 19.93/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.93/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.93/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.93/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.93/2.99  
% 19.93/2.99  ------ Combination Options
% 19.93/2.99  
% 19.93/2.99  --comb_res_mult                         3
% 19.93/2.99  --comb_sup_mult                         2
% 19.93/2.99  --comb_inst_mult                        10
% 19.93/2.99  
% 19.93/2.99  ------ Debug Options
% 19.93/2.99  
% 19.93/2.99  --dbg_backtrace                         false
% 19.93/2.99  --dbg_dump_prop_clauses                 false
% 19.93/2.99  --dbg_dump_prop_clauses_file            -
% 19.93/2.99  --dbg_out_stat                          false
% 19.93/2.99  ------ Parsing...
% 19.93/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.93/2.99  
% 19.93/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.93/2.99  
% 19.93/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.93/2.99  
% 19.93/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.93/2.99  ------ Proving...
% 19.93/2.99  ------ Problem Properties 
% 19.93/2.99  
% 19.93/2.99  
% 19.93/2.99  clauses                                 62
% 19.93/2.99  conjectures                             2
% 19.93/2.99  EPR                                     1
% 19.93/2.99  Horn                                    52
% 19.93/2.99  unary                                   25
% 19.93/2.99  binary                                  11
% 19.93/2.99  lits                                    133
% 19.93/2.99  lits eq                                 54
% 19.93/2.99  fd_pure                                 0
% 19.93/2.99  fd_pseudo                               0
% 19.93/2.99  fd_cond                                 3
% 19.93/2.99  fd_pseudo_cond                          10
% 19.93/2.99  AC symbols                              0
% 19.93/2.99  
% 19.93/2.99  ------ Schedule dynamic 5 is on 
% 19.93/2.99  
% 19.93/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.93/2.99  
% 19.93/2.99  
% 19.93/2.99  ------ 
% 19.93/2.99  Current options:
% 19.93/2.99  ------ 
% 19.93/2.99  
% 19.93/2.99  ------ Input Options
% 19.93/2.99  
% 19.93/2.99  --out_options                           all
% 19.93/2.99  --tptp_safe_out                         true
% 19.93/2.99  --problem_path                          ""
% 19.93/2.99  --include_path                          ""
% 19.93/2.99  --clausifier                            res/vclausify_rel
% 19.93/2.99  --clausifier_options                    --mode clausify
% 19.93/2.99  --stdin                                 false
% 19.93/2.99  --stats_out                             all
% 19.93/2.99  
% 19.93/2.99  ------ General Options
% 19.93/2.99  
% 19.93/2.99  --fof                                   false
% 19.93/2.99  --time_out_real                         305.
% 19.93/2.99  --time_out_virtual                      -1.
% 19.93/2.99  --symbol_type_check                     false
% 19.93/2.99  --clausify_out                          false
% 19.93/2.99  --sig_cnt_out                           false
% 19.93/2.99  --trig_cnt_out                          false
% 19.93/2.99  --trig_cnt_out_tolerance                1.
% 19.93/2.99  --trig_cnt_out_sk_spl                   false
% 19.93/2.99  --abstr_cl_out                          false
% 19.93/2.99  
% 19.93/2.99  ------ Global Options
% 19.93/2.99  
% 19.93/2.99  --schedule                              default
% 19.93/2.99  --add_important_lit                     false
% 19.93/2.99  --prop_solver_per_cl                    1000
% 19.93/2.99  --min_unsat_core                        false
% 19.93/2.99  --soft_assumptions                      false
% 19.93/2.99  --soft_lemma_size                       3
% 19.93/2.99  --prop_impl_unit_size                   0
% 19.93/2.99  --prop_impl_unit                        []
% 19.93/2.99  --share_sel_clauses                     true
% 19.93/2.99  --reset_solvers                         false
% 19.93/2.99  --bc_imp_inh                            [conj_cone]
% 19.93/2.99  --conj_cone_tolerance                   3.
% 19.93/2.99  --extra_neg_conj                        none
% 19.93/2.99  --large_theory_mode                     true
% 19.93/2.99  --prolific_symb_bound                   200
% 19.93/2.99  --lt_threshold                          2000
% 19.93/2.99  --clause_weak_htbl                      true
% 19.93/2.99  --gc_record_bc_elim                     false
% 19.93/2.99  
% 19.93/2.99  ------ Preprocessing Options
% 19.93/2.99  
% 19.93/2.99  --preprocessing_flag                    true
% 19.93/2.99  --time_out_prep_mult                    0.1
% 19.93/2.99  --splitting_mode                        input
% 19.93/2.99  --splitting_grd                         true
% 19.93/2.99  --splitting_cvd                         false
% 19.93/2.99  --splitting_cvd_svl                     false
% 19.93/2.99  --splitting_nvd                         32
% 19.93/2.99  --sub_typing                            true
% 19.93/2.99  --prep_gs_sim                           true
% 19.93/2.99  --prep_unflatten                        true
% 19.93/2.99  --prep_res_sim                          true
% 19.93/2.99  --prep_upred                            true
% 19.93/2.99  --prep_sem_filter                       exhaustive
% 19.93/2.99  --prep_sem_filter_out                   false
% 19.93/2.99  --pred_elim                             true
% 19.93/2.99  --res_sim_input                         true
% 19.93/2.99  --eq_ax_congr_red                       true
% 19.93/2.99  --pure_diseq_elim                       true
% 19.93/2.99  --brand_transform                       false
% 19.93/2.99  --non_eq_to_eq                          false
% 19.93/2.99  --prep_def_merge                        true
% 19.93/2.99  --prep_def_merge_prop_impl              false
% 19.93/2.99  --prep_def_merge_mbd                    true
% 19.93/2.99  --prep_def_merge_tr_red                 false
% 19.93/2.99  --prep_def_merge_tr_cl                  false
% 19.93/2.99  --smt_preprocessing                     true
% 19.93/2.99  --smt_ac_axioms                         fast
% 19.93/2.99  --preprocessed_out                      false
% 19.93/2.99  --preprocessed_stats                    false
% 19.93/2.99  
% 19.93/2.99  ------ Abstraction refinement Options
% 19.93/2.99  
% 19.93/2.99  --abstr_ref                             []
% 19.93/2.99  --abstr_ref_prep                        false
% 19.93/2.99  --abstr_ref_until_sat                   false
% 19.93/2.99  --abstr_ref_sig_restrict                funpre
% 19.93/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.93/2.99  --abstr_ref_under                       []
% 19.93/2.99  
% 19.93/2.99  ------ SAT Options
% 19.93/2.99  
% 19.93/2.99  --sat_mode                              false
% 19.93/2.99  --sat_fm_restart_options                ""
% 19.93/2.99  --sat_gr_def                            false
% 19.93/2.99  --sat_epr_types                         true
% 19.93/2.99  --sat_non_cyclic_types                  false
% 19.93/2.99  --sat_finite_models                     false
% 19.93/2.99  --sat_fm_lemmas                         false
% 19.93/2.99  --sat_fm_prep                           false
% 19.93/2.99  --sat_fm_uc_incr                        true
% 19.93/2.99  --sat_out_model                         small
% 19.93/2.99  --sat_out_clauses                       false
% 19.93/2.99  
% 19.93/2.99  ------ QBF Options
% 19.93/2.99  
% 19.93/2.99  --qbf_mode                              false
% 19.93/2.99  --qbf_elim_univ                         false
% 19.93/2.99  --qbf_dom_inst                          none
% 19.93/2.99  --qbf_dom_pre_inst                      false
% 19.93/2.99  --qbf_sk_in                             false
% 19.93/2.99  --qbf_pred_elim                         true
% 19.93/2.99  --qbf_split                             512
% 19.93/2.99  
% 19.93/2.99  ------ BMC1 Options
% 19.93/2.99  
% 19.93/2.99  --bmc1_incremental                      false
% 19.93/2.99  --bmc1_axioms                           reachable_all
% 19.93/2.99  --bmc1_min_bound                        0
% 19.93/2.99  --bmc1_max_bound                        -1
% 19.93/2.99  --bmc1_max_bound_default                -1
% 19.93/2.99  --bmc1_symbol_reachability              true
% 19.93/2.99  --bmc1_property_lemmas                  false
% 19.93/2.99  --bmc1_k_induction                      false
% 19.93/2.99  --bmc1_non_equiv_states                 false
% 19.93/2.99  --bmc1_deadlock                         false
% 19.93/2.99  --bmc1_ucm                              false
% 19.93/2.99  --bmc1_add_unsat_core                   none
% 19.93/2.99  --bmc1_unsat_core_children              false
% 19.93/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.93/2.99  --bmc1_out_stat                         full
% 19.93/2.99  --bmc1_ground_init                      false
% 19.93/2.99  --bmc1_pre_inst_next_state              false
% 19.93/2.99  --bmc1_pre_inst_state                   false
% 19.93/2.99  --bmc1_pre_inst_reach_state             false
% 19.93/2.99  --bmc1_out_unsat_core                   false
% 19.93/2.99  --bmc1_aig_witness_out                  false
% 19.93/2.99  --bmc1_verbose                          false
% 19.93/2.99  --bmc1_dump_clauses_tptp                false
% 19.93/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.93/2.99  --bmc1_dump_file                        -
% 19.93/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.93/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.93/2.99  --bmc1_ucm_extend_mode                  1
% 19.93/2.99  --bmc1_ucm_init_mode                    2
% 19.93/2.99  --bmc1_ucm_cone_mode                    none
% 19.93/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.93/2.99  --bmc1_ucm_relax_model                  4
% 19.93/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.93/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.93/2.99  --bmc1_ucm_layered_model                none
% 19.93/2.99  --bmc1_ucm_max_lemma_size               10
% 19.93/2.99  
% 19.93/2.99  ------ AIG Options
% 19.93/2.99  
% 19.93/2.99  --aig_mode                              false
% 19.93/2.99  
% 19.93/2.99  ------ Instantiation Options
% 19.93/2.99  
% 19.93/2.99  --instantiation_flag                    true
% 19.93/2.99  --inst_sos_flag                         false
% 19.93/2.99  --inst_sos_phase                        true
% 19.93/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.93/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.93/2.99  --inst_lit_sel_side                     none
% 19.93/2.99  --inst_solver_per_active                1400
% 19.93/2.99  --inst_solver_calls_frac                1.
% 19.93/2.99  --inst_passive_queue_type               priority_queues
% 19.93/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.93/2.99  --inst_passive_queues_freq              [25;2]
% 19.93/2.99  --inst_dismatching                      true
% 19.93/2.99  --inst_eager_unprocessed_to_passive     true
% 19.93/2.99  --inst_prop_sim_given                   true
% 19.93/2.99  --inst_prop_sim_new                     false
% 19.93/2.99  --inst_subs_new                         false
% 19.93/2.99  --inst_eq_res_simp                      false
% 19.93/2.99  --inst_subs_given                       false
% 19.93/2.99  --inst_orphan_elimination               true
% 19.93/2.99  --inst_learning_loop_flag               true
% 19.93/2.99  --inst_learning_start                   3000
% 19.93/2.99  --inst_learning_factor                  2
% 19.93/2.99  --inst_start_prop_sim_after_learn       3
% 19.93/2.99  --inst_sel_renew                        solver
% 19.93/2.99  --inst_lit_activity_flag                true
% 19.93/2.99  --inst_restr_to_given                   false
% 19.93/2.99  --inst_activity_threshold               500
% 19.93/2.99  --inst_out_proof                        true
% 19.93/2.99  
% 19.93/2.99  ------ Resolution Options
% 19.93/2.99  
% 19.93/2.99  --resolution_flag                       false
% 19.93/2.99  --res_lit_sel                           adaptive
% 19.93/2.99  --res_lit_sel_side                      none
% 19.93/2.99  --res_ordering                          kbo
% 19.93/2.99  --res_to_prop_solver                    active
% 19.93/2.99  --res_prop_simpl_new                    false
% 19.93/2.99  --res_prop_simpl_given                  true
% 19.93/2.99  --res_passive_queue_type                priority_queues
% 19.93/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.93/2.99  --res_passive_queues_freq               [15;5]
% 19.93/2.99  --res_forward_subs                      full
% 19.93/2.99  --res_backward_subs                     full
% 19.93/2.99  --res_forward_subs_resolution           true
% 19.93/2.99  --res_backward_subs_resolution          true
% 19.93/2.99  --res_orphan_elimination                true
% 19.93/2.99  --res_time_limit                        2.
% 19.93/2.99  --res_out_proof                         true
% 19.93/2.99  
% 19.93/2.99  ------ Superposition Options
% 19.93/2.99  
% 19.93/2.99  --superposition_flag                    true
% 19.93/2.99  --sup_passive_queue_type                priority_queues
% 19.93/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.93/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.93/2.99  --demod_completeness_check              fast
% 19.93/2.99  --demod_use_ground                      true
% 19.93/2.99  --sup_to_prop_solver                    passive
% 19.93/2.99  --sup_prop_simpl_new                    true
% 19.93/2.99  --sup_prop_simpl_given                  true
% 19.93/2.99  --sup_fun_splitting                     false
% 19.93/2.99  --sup_smt_interval                      50000
% 19.93/2.99  
% 19.93/2.99  ------ Superposition Simplification Setup
% 19.93/2.99  
% 19.93/2.99  --sup_indices_passive                   []
% 19.93/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.93/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.93/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.93/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.93/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.93/2.99  --sup_full_bw                           [BwDemod]
% 19.93/2.99  --sup_immed_triv                        [TrivRules]
% 19.93/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.93/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.93/2.99  --sup_immed_bw_main                     []
% 19.93/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.93/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.93/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.93/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.93/2.99  
% 19.93/2.99  ------ Combination Options
% 19.93/2.99  
% 19.93/2.99  --comb_res_mult                         3
% 19.93/2.99  --comb_sup_mult                         2
% 19.93/2.99  --comb_inst_mult                        10
% 19.93/2.99  
% 19.93/2.99  ------ Debug Options
% 19.93/2.99  
% 19.93/2.99  --dbg_backtrace                         false
% 19.93/2.99  --dbg_dump_prop_clauses                 false
% 19.93/2.99  --dbg_dump_prop_clauses_file            -
% 19.93/2.99  --dbg_out_stat                          false
% 19.93/2.99  
% 19.93/2.99  
% 19.93/2.99  
% 19.93/2.99  
% 19.93/2.99  ------ Proving...
% 19.93/2.99  
% 19.93/2.99  
% 19.93/2.99  % SZS status Theorem for theBenchmark.p
% 19.93/2.99  
% 19.93/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.93/2.99  
% 19.93/2.99  fof(f16,axiom,(
% 19.93/2.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f131,plain,(
% 19.93/2.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 19.93/2.99    inference(cnf_transformation,[],[f16])).
% 19.93/2.99  
% 19.93/2.99  fof(f11,axiom,(
% 19.93/2.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f83,plain,(
% 19.93/2.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.93/2.99    inference(nnf_transformation,[],[f11])).
% 19.93/2.99  
% 19.93/2.99  fof(f84,plain,(
% 19.93/2.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.93/2.99    inference(flattening,[],[f83])).
% 19.93/2.99  
% 19.93/2.99  fof(f122,plain,(
% 19.93/2.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 19.93/2.99    inference(cnf_transformation,[],[f84])).
% 19.93/2.99  
% 19.93/2.99  fof(f168,plain,(
% 19.93/2.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 19.93/2.99    inference(equality_resolution,[],[f122])).
% 19.93/2.99  
% 19.93/2.99  fof(f21,axiom,(
% 19.93/2.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f141,plain,(
% 19.93/2.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 19.93/2.99    inference(cnf_transformation,[],[f21])).
% 19.93/2.99  
% 19.93/2.99  fof(f36,conjecture,(
% 19.93/2.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f37,negated_conjecture,(
% 19.93/2.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 19.93/2.99    inference(negated_conjecture,[],[f36])).
% 19.93/2.99  
% 19.93/2.99  fof(f65,plain,(
% 19.93/2.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 19.93/2.99    inference(ennf_transformation,[],[f37])).
% 19.93/2.99  
% 19.93/2.99  fof(f96,plain,(
% 19.93/2.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)) & v1_relat_1(sK8))),
% 19.93/2.99    introduced(choice_axiom,[])).
% 19.93/2.99  
% 19.93/2.99  fof(f97,plain,(
% 19.93/2.99    (k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)) & v1_relat_1(sK8)),
% 19.93/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f65,f96])).
% 19.93/2.99  
% 19.93/2.99  fof(f158,plain,(
% 19.93/2.99    v1_relat_1(sK8)),
% 19.93/2.99    inference(cnf_transformation,[],[f97])).
% 19.93/2.99  
% 19.93/2.99  fof(f20,axiom,(
% 19.93/2.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f44,plain,(
% 19.93/2.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 19.93/2.99    inference(ennf_transformation,[],[f20])).
% 19.93/2.99  
% 19.93/2.99  fof(f45,plain,(
% 19.93/2.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 19.93/2.99    inference(flattening,[],[f44])).
% 19.93/2.99  
% 19.93/2.99  fof(f140,plain,(
% 19.93/2.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f45])).
% 19.93/2.99  
% 19.93/2.99  fof(f26,axiom,(
% 19.93/2.99    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f53,plain,(
% 19.93/2.99    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 19.93/2.99    inference(ennf_transformation,[],[f26])).
% 19.93/2.99  
% 19.93/2.99  fof(f147,plain,(
% 19.93/2.99    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f53])).
% 19.93/2.99  
% 19.93/2.99  fof(f35,axiom,(
% 19.93/2.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f156,plain,(
% 19.93/2.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 19.93/2.99    inference(cnf_transformation,[],[f35])).
% 19.93/2.99  
% 19.93/2.99  fof(f31,axiom,(
% 19.93/2.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f59,plain,(
% 19.93/2.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.93/2.99    inference(ennf_transformation,[],[f31])).
% 19.93/2.99  
% 19.93/2.99  fof(f60,plain,(
% 19.93/2.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.93/2.99    inference(flattening,[],[f59])).
% 19.93/2.99  
% 19.93/2.99  fof(f152,plain,(
% 19.93/2.99    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f60])).
% 19.93/2.99  
% 19.93/2.99  fof(f157,plain,(
% 19.93/2.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 19.93/2.99    inference(cnf_transformation,[],[f35])).
% 19.93/2.99  
% 19.93/2.99  fof(f8,axiom,(
% 19.93/2.99    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f112,plain,(
% 19.93/2.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f8])).
% 19.93/2.99  
% 19.93/2.99  fof(f5,axiom,(
% 19.93/2.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f76,plain,(
% 19.93/2.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 19.93/2.99    inference(nnf_transformation,[],[f5])).
% 19.93/2.99  
% 19.93/2.99  fof(f108,plain,(
% 19.93/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f76])).
% 19.93/2.99  
% 19.93/2.99  fof(f7,axiom,(
% 19.93/2.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f111,plain,(
% 19.93/2.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f7])).
% 19.93/2.99  
% 19.93/2.99  fof(f15,axiom,(
% 19.93/2.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f42,plain,(
% 19.93/2.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 19.93/2.99    inference(ennf_transformation,[],[f15])).
% 19.93/2.99  
% 19.93/2.99  fof(f130,plain,(
% 19.93/2.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f42])).
% 19.93/2.99  
% 19.93/2.99  fof(f30,axiom,(
% 19.93/2.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f57,plain,(
% 19.93/2.99    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.93/2.99    inference(ennf_transformation,[],[f30])).
% 19.93/2.99  
% 19.93/2.99  fof(f58,plain,(
% 19.93/2.99    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.93/2.99    inference(flattening,[],[f57])).
% 19.93/2.99  
% 19.93/2.99  fof(f151,plain,(
% 19.93/2.99    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f58])).
% 19.93/2.99  
% 19.93/2.99  fof(f25,axiom,(
% 19.93/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f51,plain,(
% 19.93/2.99    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 19.93/2.99    inference(ennf_transformation,[],[f25])).
% 19.93/2.99  
% 19.93/2.99  fof(f52,plain,(
% 19.93/2.99    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 19.93/2.99    inference(flattening,[],[f51])).
% 19.93/2.99  
% 19.93/2.99  fof(f145,plain,(
% 19.93/2.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f52])).
% 19.93/2.99  
% 19.93/2.99  fof(f34,axiom,(
% 19.93/2.99    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 19.93/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.93/2.99  
% 19.93/2.99  fof(f63,plain,(
% 19.93/2.99    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 19.93/2.99    inference(ennf_transformation,[],[f34])).
% 19.93/2.99  
% 19.93/2.99  fof(f64,plain,(
% 19.93/2.99    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 19.93/2.99    inference(flattening,[],[f63])).
% 19.93/2.99  
% 19.93/2.99  fof(f94,plain,(
% 19.93/2.99    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0))),
% 19.93/2.99    introduced(choice_axiom,[])).
% 19.93/2.99  
% 19.93/2.99  fof(f95,plain,(
% 19.93/2.99    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | ~v1_relat_1(X0))),
% 19.93/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f64,f94])).
% 19.93/2.99  
% 19.93/2.99  fof(f155,plain,(
% 19.93/2.99    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | ~v1_relat_1(X0)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f95])).
% 19.93/2.99  
% 19.93/2.99  fof(f121,plain,(
% 19.93/2.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 19.93/2.99    inference(cnf_transformation,[],[f84])).
% 19.93/2.99  
% 19.93/2.99  fof(f169,plain,(
% 19.93/2.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 19.93/2.99    inference(equality_resolution,[],[f121])).
% 19.93/2.99  
% 19.93/2.99  fof(f120,plain,(
% 19.93/2.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 19.93/2.99    inference(cnf_transformation,[],[f84])).
% 19.93/2.99  
% 19.93/2.99  fof(f159,plain,(
% 19.93/2.99    k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8)),
% 19.93/2.99    inference(cnf_transformation,[],[f97])).
% 19.93/2.99  
% 19.93/2.99  cnf(c_33,plain,
% 19.93/2.99      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f131]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_93754,plain,
% 19.93/2.99      ( k2_xboole_0(k1_tarski(sK6(k5_relat_1(k1_xboole_0,sK8))),k1_relat_1(k5_relat_1(k1_xboole_0,sK8))) != k1_xboole_0 ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_33]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_22,plain,
% 19.93/2.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f168]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_43,plain,
% 19.93/2.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 19.93/2.99      inference(cnf_transformation,[],[f141]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_2658,plain,
% 19.93/2.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 19.93/2.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_3351,plain,
% 19.93/2.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 19.93/2.99      inference(superposition,[status(thm)],[c_22,c_2658]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_61,negated_conjecture,
% 19.93/2.99      ( v1_relat_1(sK8) ),
% 19.93/2.99      inference(cnf_transformation,[],[f158]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_2643,plain,
% 19.93/2.99      ( v1_relat_1(sK8) = iProver_top ),
% 19.93/2.99      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_42,plain,
% 19.93/2.99      ( ~ v1_relat_1(X0)
% 19.93/2.99      | ~ v1_relat_1(X1)
% 19.93/2.99      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 19.93/2.99      inference(cnf_transformation,[],[f140]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_2659,plain,
% 19.93/2.99      ( v1_relat_1(X0) != iProver_top
% 19.93/2.99      | v1_relat_1(X1) != iProver_top
% 19.93/2.99      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 19.93/2.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_49,plain,
% 19.93/2.99      ( ~ v1_relat_1(X0)
% 19.93/2.99      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f147]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_2652,plain,
% 19.93/2.99      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
% 19.93/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.93/2.99      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_7974,plain,
% 19.93/2.99      ( k3_xboole_0(k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1)))) = k5_relat_1(X0,X1)
% 19.93/2.99      | v1_relat_1(X1) != iProver_top
% 19.93/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.93/2.99      inference(superposition,[status(thm)],[c_2659,c_2652]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_83785,plain,
% 19.93/2.99      ( k3_xboole_0(k5_relat_1(sK8,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK8,X0)),k2_relat_1(k5_relat_1(sK8,X0)))) = k5_relat_1(sK8,X0)
% 19.93/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.93/2.99      inference(superposition,[status(thm)],[c_2643,c_7974]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_84300,plain,
% 19.93/2.99      ( k3_xboole_0(k5_relat_1(sK8,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK8,k1_xboole_0)),k2_relat_1(k5_relat_1(sK8,k1_xboole_0)))) = k5_relat_1(sK8,k1_xboole_0) ),
% 19.93/2.99      inference(superposition,[status(thm)],[c_3351,c_83785]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_59,plain,
% 19.93/2.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f156]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_54,plain,
% 19.93/2.99      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 19.93/2.99      | ~ v1_relat_1(X1)
% 19.93/2.99      | ~ v1_relat_1(X0)
% 19.93/2.99      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 19.93/2.99      inference(cnf_transformation,[],[f152]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_2647,plain,
% 19.93/2.99      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 19.93/2.99      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 19.93/2.99      | v1_relat_1(X1) != iProver_top
% 19.93/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.93/2.99      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_4680,plain,
% 19.93/2.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 19.93/2.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 19.93/2.99      | v1_relat_1(X0) != iProver_top
% 19.93/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.93/2.99      inference(superposition,[status(thm)],[c_59,c_2647]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_58,plain,
% 19.93/2.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f157]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_4694,plain,
% 19.93/2.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 19.93/2.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 19.93/2.99      | v1_relat_1(X0) != iProver_top
% 19.93/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.93/2.99      inference(light_normalisation,[status(thm)],[c_4680,c_58]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_16436,plain,
% 19.93/2.99      ( v1_relat_1(X0) != iProver_top
% 19.93/2.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 19.93/2.99      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.93/2.99      inference(global_propositional_subsumption,
% 19.93/2.99                [status(thm)],
% 19.93/2.99                [c_4694,c_3351]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_16437,plain,
% 19.93/2.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 19.93/2.99      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 19.93/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.93/2.99      inference(renaming,[status(thm)],[c_16436]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_14,plain,
% 19.93/2.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f112]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_11,plain,
% 19.93/2.99      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f108]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_2675,plain,
% 19.93/2.99      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 19.93/2.99      | r1_tarski(X0,X1) = iProver_top ),
% 19.93/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_6330,plain,
% 19.93/2.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.93/2.99      inference(superposition,[status(thm)],[c_14,c_2675]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_16443,plain,
% 19.93/2.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 19.93/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.93/2.99      inference(forward_subsumption_resolution,
% 19.93/2.99                [status(thm)],
% 19.93/2.99                [c_16437,c_6330]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_16449,plain,
% 19.93/2.99      ( k2_relat_1(k5_relat_1(sK8,k1_xboole_0)) = k1_xboole_0 ),
% 19.93/2.99      inference(superposition,[status(thm)],[c_2643,c_16443]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_84423,plain,
% 19.93/2.99      ( k3_xboole_0(k5_relat_1(sK8,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK8,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(sK8,k1_xboole_0) ),
% 19.93/2.99      inference(light_normalisation,[status(thm)],[c_84300,c_16449]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_13,plain,
% 19.93/2.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f111]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_84424,plain,
% 19.93/2.99      ( k5_relat_1(sK8,k1_xboole_0) = k1_xboole_0 ),
% 19.93/2.99      inference(demodulation,[status(thm)],[c_84423,c_13,c_22]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_1684,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_81846,plain,
% 19.93/2.99      ( X0 != X1
% 19.93/2.99      | X0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK8))
% 19.93/2.99      | k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) != X1 ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_1684]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_81847,plain,
% 19.93/2.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) != k1_xboole_0
% 19.93/2.99      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK8))
% 19.93/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_81846]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_3223,plain,
% 19.93/2.99      ( k2_xboole_0(k1_tarski(X0),X1) != X2
% 19.93/2.99      | k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
% 19.93/2.99      | k1_xboole_0 != X2 ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_1684]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_71382,plain,
% 19.93/2.99      ( k2_xboole_0(k1_tarski(sK6(k5_relat_1(k1_xboole_0,sK8))),k1_relat_1(k5_relat_1(k1_xboole_0,sK8))) != k1_relat_1(k5_relat_1(k1_xboole_0,sK8))
% 19.93/2.99      | k2_xboole_0(k1_tarski(sK6(k5_relat_1(k1_xboole_0,sK8))),k1_relat_1(k5_relat_1(k1_xboole_0,sK8))) = k1_xboole_0
% 19.93/2.99      | k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_3223]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_32,plain,
% 19.93/2.99      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 19.93/2.99      inference(cnf_transformation,[],[f130]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_23750,plain,
% 19.93/2.99      ( ~ r2_hidden(sK6(k5_relat_1(k1_xboole_0,sK8)),k1_relat_1(k5_relat_1(k1_xboole_0,sK8)))
% 19.93/2.99      | k2_xboole_0(k1_tarski(sK6(k5_relat_1(k1_xboole_0,sK8))),k1_relat_1(k5_relat_1(k1_xboole_0,sK8))) = k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_32]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_53,plain,
% 19.93/2.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 19.93/2.99      | ~ v1_relat_1(X1)
% 19.93/2.99      | ~ v1_relat_1(X0)
% 19.93/2.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 19.93/2.99      inference(cnf_transformation,[],[f151]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_2648,plain,
% 19.93/2.99      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 19.93/2.99      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 19.93/2.99      | v1_relat_1(X0) != iProver_top
% 19.93/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.93/2.99      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_5651,plain,
% 19.93/2.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 19.93/2.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 19.93/2.99      | v1_relat_1(X0) != iProver_top
% 19.93/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.93/2.99      inference(superposition,[status(thm)],[c_58,c_2648]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_5665,plain,
% 19.93/2.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 19.93/2.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 19.93/2.99      | v1_relat_1(X0) != iProver_top
% 19.93/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.93/2.99      inference(light_normalisation,[status(thm)],[c_5651,c_59]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_16503,plain,
% 19.93/2.99      ( v1_relat_1(X0) != iProver_top
% 19.93/2.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 19.93/2.99      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 19.93/2.99      inference(global_propositional_subsumption,
% 19.93/2.99                [status(thm)],
% 19.93/2.99                [c_5665,c_3351]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_16504,plain,
% 19.93/2.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 19.93/2.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 19.93/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.93/2.99      inference(renaming,[status(thm)],[c_16503]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_16510,plain,
% 19.93/2.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 19.93/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.93/2.99      inference(forward_subsumption_resolution,
% 19.93/2.99                [status(thm)],
% 19.93/2.99                [c_16504,c_6330]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_16516,plain,
% 19.93/2.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK8)) = k1_xboole_0 ),
% 19.93/2.99      inference(superposition,[status(thm)],[c_2643,c_16510]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_48,plain,
% 19.93/2.99      ( r2_hidden(X0,k1_relat_1(X1))
% 19.93/2.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.93/2.99      | ~ v1_relat_1(X1) ),
% 19.93/2.99      inference(cnf_transformation,[],[f145]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_3359,plain,
% 19.93/2.99      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK8)))
% 19.93/2.99      | ~ r2_hidden(k4_tarski(X0,X2),k5_relat_1(X1,sK8))
% 19.93/2.99      | ~ v1_relat_1(k5_relat_1(X1,sK8)) ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_48]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_4416,plain,
% 19.93/2.99      ( ~ r2_hidden(k4_tarski(sK6(k5_relat_1(k1_xboole_0,sK8)),sK7(k5_relat_1(k1_xboole_0,sK8))),k5_relat_1(k1_xboole_0,sK8))
% 19.93/2.99      | r2_hidden(sK6(k5_relat_1(k1_xboole_0,sK8)),k1_relat_1(k5_relat_1(k1_xboole_0,sK8)))
% 19.93/2.99      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK8)) ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_3359]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_57,plain,
% 19.93/2.99      ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
% 19.93/2.99      | ~ v1_relat_1(X0)
% 19.93/2.99      | k1_xboole_0 = X0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f155]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_3454,plain,
% 19.93/2.99      ( r2_hidden(k4_tarski(sK6(k5_relat_1(k1_xboole_0,sK8)),sK7(k5_relat_1(k1_xboole_0,sK8))),k5_relat_1(k1_xboole_0,sK8))
% 19.93/2.99      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK8))
% 19.93/2.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK8) ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_57]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_3353,plain,
% 19.93/2.99      ( v1_relat_1(k1_xboole_0) ),
% 19.93/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_3351]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_3226,plain,
% 19.93/2.99      ( k5_relat_1(sK8,k1_xboole_0) != X0
% 19.93/2.99      | k1_xboole_0 != X0
% 19.93/2.99      | k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0) ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_1684]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_3227,plain,
% 19.93/2.99      ( k5_relat_1(sK8,k1_xboole_0) != k1_xboole_0
% 19.93/2.99      | k1_xboole_0 = k5_relat_1(sK8,k1_xboole_0)
% 19.93/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_3226]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_3090,plain,
% 19.93/2.99      ( ~ v1_relat_1(X0)
% 19.93/2.99      | v1_relat_1(k5_relat_1(X0,sK8))
% 19.93/2.99      | ~ v1_relat_1(sK8) ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_42]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_3092,plain,
% 19.93/2.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK8))
% 19.93/2.99      | ~ v1_relat_1(sK8)
% 19.93/2.99      | ~ v1_relat_1(k1_xboole_0) ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_3090]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_23,plain,
% 19.93/2.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.93/2.99      inference(cnf_transformation,[],[f169]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_141,plain,
% 19.93/2.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_23]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_24,plain,
% 19.93/2.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 19.93/2.99      | k1_xboole_0 = X0
% 19.93/2.99      | k1_xboole_0 = X1 ),
% 19.93/2.99      inference(cnf_transformation,[],[f120]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_140,plain,
% 19.93/2.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.93/2.99      | k1_xboole_0 = k1_xboole_0 ),
% 19.93/2.99      inference(instantiation,[status(thm)],[c_24]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(c_60,negated_conjecture,
% 19.93/2.99      ( k1_xboole_0 != k5_relat_1(sK8,k1_xboole_0)
% 19.93/2.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK8) ),
% 19.93/2.99      inference(cnf_transformation,[],[f159]) ).
% 19.93/2.99  
% 19.93/2.99  cnf(contradiction,plain,
% 19.93/2.99      ( $false ),
% 19.93/2.99      inference(minisat,
% 19.93/2.99                [status(thm)],
% 19.93/2.99                [c_93754,c_84424,c_81847,c_71382,c_23750,c_16516,c_4416,
% 19.93/2.99                 c_3454,c_3353,c_3227,c_3092,c_141,c_140,c_60,c_61]) ).
% 19.93/2.99  
% 19.93/2.99  
% 19.93/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.93/2.99  
% 19.93/2.99  ------                               Statistics
% 19.93/2.99  
% 19.93/2.99  ------ General
% 19.93/2.99  
% 19.93/2.99  abstr_ref_over_cycles:                  0
% 19.93/2.99  abstr_ref_under_cycles:                 0
% 19.93/2.99  gc_basic_clause_elim:                   0
% 19.93/2.99  forced_gc_time:                         0
% 19.93/2.99  parsing_time:                           0.011
% 19.93/2.99  unif_index_cands_time:                  0.
% 19.93/2.99  unif_index_add_time:                    0.
% 19.93/2.99  orderings_time:                         0.
% 19.93/2.99  out_proof_time:                         0.015
% 19.93/2.99  total_time:                             2.344
% 19.93/2.99  num_of_symbols:                         56
% 19.93/2.99  num_of_terms:                           93292
% 19.93/2.99  
% 19.93/2.99  ------ Preprocessing
% 19.93/2.99  
% 19.93/2.99  num_of_splits:                          0
% 19.93/2.99  num_of_split_atoms:                     0
% 19.93/2.99  num_of_reused_defs:                     0
% 19.93/2.99  num_eq_ax_congr_red:                    24
% 19.93/2.99  num_of_sem_filtered_clauses:            1
% 19.93/2.99  num_of_subtypes:                        0
% 19.93/2.99  monotx_restored_types:                  0
% 19.93/2.99  sat_num_of_epr_types:                   0
% 19.93/2.99  sat_num_of_non_cyclic_types:            0
% 19.93/2.99  sat_guarded_non_collapsed_types:        0
% 19.93/2.99  num_pure_diseq_elim:                    0
% 19.93/2.99  simp_replaced_by:                       0
% 19.93/2.99  res_preprocessed:                       221
% 19.93/2.99  prep_upred:                             0
% 19.93/2.99  prep_unflattend:                        48
% 19.93/2.99  smt_new_axioms:                         0
% 19.93/2.99  pred_elim_cands:                        3
% 19.93/2.99  pred_elim:                              0
% 19.93/2.99  pred_elim_cl:                           0
% 19.93/2.99  pred_elim_cycles:                       1
% 19.93/2.99  merged_defs:                            12
% 19.93/2.99  merged_defs_ncl:                        0
% 19.93/2.99  bin_hyper_res:                          12
% 19.93/2.99  prep_cycles:                            3
% 19.93/2.99  pred_elim_time:                         0.02
% 19.93/2.99  splitting_time:                         0.
% 19.93/2.99  sem_filter_time:                        0.
% 19.93/2.99  monotx_time:                            0.
% 19.93/2.99  subtype_inf_time:                       0.
% 19.93/2.99  
% 19.93/2.99  ------ Problem properties
% 19.93/2.99  
% 19.93/2.99  clauses:                                62
% 19.93/2.99  conjectures:                            2
% 19.93/2.99  epr:                                    1
% 19.93/2.99  horn:                                   52
% 19.93/2.99  ground:                                 5
% 19.93/2.99  unary:                                  25
% 19.93/2.99  binary:                                 11
% 19.93/2.99  lits:                                   133
% 19.93/2.99  lits_eq:                                54
% 19.93/2.99  fd_pure:                                0
% 19.93/2.99  fd_pseudo:                              0
% 19.93/2.99  fd_cond:                                3
% 19.93/2.99  fd_pseudo_cond:                         10
% 19.93/2.99  ac_symbols:                             0
% 19.93/2.99  
% 19.93/2.99  ------ Propositional Solver
% 19.93/2.99  
% 19.93/2.99  prop_solver_calls:                      39
% 19.93/2.99  prop_fast_solver_calls:                 2644
% 19.93/2.99  smt_solver_calls:                       0
% 19.93/2.99  smt_fast_solver_calls:                  0
% 19.93/2.99  prop_num_of_clauses:                    36768
% 19.93/2.99  prop_preprocess_simplified:             61212
% 19.93/2.99  prop_fo_subsumed:                       114
% 19.93/2.99  prop_solver_time:                       0.
% 19.93/2.99  smt_solver_time:                        0.
% 19.93/2.99  smt_fast_solver_time:                   0.
% 19.93/2.99  prop_fast_solver_time:                  0.
% 19.93/2.99  prop_unsat_core_time:                   0.004
% 19.93/2.99  
% 19.93/2.99  ------ QBF
% 19.93/2.99  
% 19.93/2.99  qbf_q_res:                              0
% 19.93/2.99  qbf_num_tautologies:                    0
% 19.93/2.99  qbf_prep_cycles:                        0
% 19.93/2.99  
% 19.93/2.99  ------ BMC1
% 19.93/2.99  
% 19.93/2.99  bmc1_current_bound:                     -1
% 19.93/2.99  bmc1_last_solved_bound:                 -1
% 19.93/2.99  bmc1_unsat_core_size:                   -1
% 19.93/2.99  bmc1_unsat_core_parents_size:           -1
% 19.93/2.99  bmc1_merge_next_fun:                    0
% 19.93/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.93/2.99  
% 19.93/2.99  ------ Instantiation
% 19.93/2.99  
% 19.93/2.99  inst_num_of_clauses:                    1131
% 19.93/2.99  inst_num_in_passive:                    325
% 19.93/2.99  inst_num_in_active:                     1902
% 19.93/2.99  inst_num_in_unprocessed:                471
% 19.93/2.99  inst_num_of_loops:                      3349
% 19.93/2.99  inst_num_of_learning_restarts:          1
% 19.93/2.99  inst_num_moves_active_passive:          1443
% 19.93/2.99  inst_lit_activity:                      0
% 19.93/2.99  inst_lit_activity_moves:                0
% 19.93/2.99  inst_num_tautologies:                   0
% 19.93/2.99  inst_num_prop_implied:                  0
% 19.93/2.99  inst_num_existing_simplified:           0
% 19.93/2.99  inst_num_eq_res_simplified:             0
% 19.93/2.99  inst_num_child_elim:                    0
% 19.93/2.99  inst_num_of_dismatching_blockings:      4454
% 19.93/2.99  inst_num_of_non_proper_insts:           6917
% 19.93/2.99  inst_num_of_duplicates:                 0
% 19.93/2.99  inst_inst_num_from_inst_to_res:         0
% 19.93/2.99  inst_dismatching_checking_time:         0.
% 19.93/2.99  
% 19.93/2.99  ------ Resolution
% 19.93/2.99  
% 19.93/2.99  res_num_of_clauses:                     79
% 19.93/2.99  res_num_in_passive:                     79
% 19.93/2.99  res_num_in_active:                      0
% 19.93/2.99  res_num_of_loops:                       224
% 19.93/2.99  res_forward_subset_subsumed:            295
% 19.93/2.99  res_backward_subset_subsumed:           0
% 19.93/2.99  res_forward_subsumed:                   1
% 19.93/2.99  res_backward_subsumed:                  0
% 19.93/2.99  res_forward_subsumption_resolution:     0
% 19.93/2.99  res_backward_subsumption_resolution:    0
% 19.93/2.99  res_clause_to_clause_subsumption:       14812
% 19.93/2.99  res_orphan_elimination:                 0
% 19.93/2.99  res_tautology_del:                      284
% 19.93/2.99  res_num_eq_res_simplified:              0
% 19.93/2.99  res_num_sel_changes:                    0
% 19.93/2.99  res_moves_from_active_to_pass:          0
% 19.93/2.99  
% 19.93/2.99  ------ Superposition
% 19.93/2.99  
% 19.93/2.99  sup_time_total:                         0.
% 19.93/2.99  sup_time_generating:                    0.
% 19.93/2.99  sup_time_sim_full:                      0.
% 19.93/2.99  sup_time_sim_immed:                     0.
% 19.93/2.99  
% 19.93/2.99  sup_num_of_clauses:                     3476
% 19.93/2.99  sup_num_in_active:                      521
% 19.93/2.99  sup_num_in_passive:                     2955
% 19.93/2.99  sup_num_of_loops:                       668
% 19.93/2.99  sup_fw_superposition:                   2475
% 19.93/2.99  sup_bw_superposition:                   2226
% 19.93/2.99  sup_immediate_simplified:               737
% 19.93/2.99  sup_given_eliminated:                   1
% 19.93/2.99  comparisons_done:                       0
% 19.93/2.99  comparisons_avoided:                    37
% 19.93/2.99  
% 19.93/2.99  ------ Simplifications
% 19.93/2.99  
% 19.93/2.99  
% 19.93/2.99  sim_fw_subset_subsumed:                 160
% 19.93/2.99  sim_bw_subset_subsumed:                 35
% 19.93/2.99  sim_fw_subsumed:                        159
% 19.93/2.99  sim_bw_subsumed:                        2
% 19.93/2.99  sim_fw_subsumption_res:                 11
% 19.93/2.99  sim_bw_subsumption_res:                 0
% 19.93/2.99  sim_tautology_del:                      66
% 19.93/2.99  sim_eq_tautology_del:                   217
% 19.93/2.99  sim_eq_res_simp:                        10
% 19.93/2.99  sim_fw_demodulated:                     99
% 19.93/2.99  sim_bw_demodulated:                     159
% 19.93/2.99  sim_light_normalised:                   426
% 19.93/2.99  sim_joinable_taut:                      0
% 19.93/2.99  sim_joinable_simp:                      0
% 19.93/2.99  sim_ac_normalised:                      0
% 19.93/2.99  sim_smt_subsumption:                    0
% 19.93/2.99  
%------------------------------------------------------------------------------

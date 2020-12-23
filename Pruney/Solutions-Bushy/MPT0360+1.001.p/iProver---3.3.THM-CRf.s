%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0360+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:06 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   44 (  62 expanded)
%              Number of clauses        :   25 (  25 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 196 expanded)
%              Number of equality atoms :   46 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_139,plain,
    ( ~ r1_tarski(X0_38,X0_39)
    | r1_tarski(X1_38,X1_39)
    | X1_39 != X0_39
    | X1_38 != X0_38 ),
    theory(equality)).

cnf(c_238,plain,
    ( ~ r1_tarski(X0_38,X0_39)
    | r1_tarski(X1_38,k4_xboole_0(X0_40,X1_39))
    | k4_xboole_0(X0_40,X1_39) != X0_39
    | X1_38 != X0_38 ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_251,plain,
    ( r1_tarski(X0_38,k4_xboole_0(X0_40,sK2))
    | ~ r1_tarski(X1_38,k3_subset_1(X0_40,sK2))
    | k4_xboole_0(X0_40,sK2) != k3_subset_1(X0_40,sK2)
    | X0_38 != X1_38 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_253,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | k4_xboole_0(sK0,sK2) != k3_subset_1(sK0,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_133,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_231,plain,
    ( k1_zfmisc_1(sK0) = k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X2,X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_81,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | X3 != X2
    | k4_xboole_0(X4,X3) != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_82,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_81])).

cnf(c_125,plain,
    ( ~ r1_tarski(X0_38,X0_39)
    | ~ r1_tarski(X0_38,k4_xboole_0(X0_40,X0_39))
    | k1_xboole_0 = X0_38 ),
    inference(subtyping,[status(esa)],[c_82])).

cnf(c_151,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_70,plain,
    ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_71,plain,
    ( k4_xboole_0(X0,sK2) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK0) ),
    inference(unflattening,[status(thm)],[c_70])).

cnf(c_126,plain,
    ( k1_zfmisc_1(X0_40) != k1_zfmisc_1(sK0)
    | k4_xboole_0(X0_40,sK2) = k3_subset_1(X0_40,sK2) ),
    inference(subtyping,[status(esa)],[c_71])).

cnf(c_149,plain,
    ( k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0)
    | k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_3,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_129,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_131,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_144,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_253,c_231,c_151,c_149,c_129,c_144,c_4,c_5])).


%------------------------------------------------------------------------------

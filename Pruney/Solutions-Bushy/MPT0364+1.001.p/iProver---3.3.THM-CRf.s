%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0364+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:06 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   14
%              Number of atoms          :  176 ( 346 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(X1,sK2)
          | ~ r1_xboole_0(X1,k3_subset_1(X0,sK2)) )
        & ( r1_tarski(X1,sK2)
          | r1_xboole_0(X1,k3_subset_1(X0,sK2)) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14,f13])).

fof(f23,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_3,plain,
    ( r1_tarski(X0,k3_subset_1(X1,X2))
    | ~ r1_xboole_0(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,negated_conjecture,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_60,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_186,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k3_subset_1(X2,X1) != sK2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_60])).

cnf(c_187,plain,
    ( ~ r1_xboole_0(sK1,X0)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_286,plain,
    ( ~ r1_xboole_0(sK1,X0_36)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(X0_37))
    | k3_subset_1(X0_37,X0_36) != sK2 ),
    inference(subtyping,[status(esa)],[c_187])).

cnf(c_560,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(X0_37))
    | k3_subset_1(X0_37,k3_subset_1(sK0,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_562,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_37))
    | m1_subset_1(k3_subset_1(X0_37,X0_36),k1_zfmisc_1(X0_37)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_506,plain,
    ( m1_subset_1(k3_subset_1(X0_37,sK2),k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_37)) ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_508,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_xboole_0(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_62,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_207,plain,
    ( r1_xboole_0(X0,X1)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k3_subset_1(X2,X1) != sK2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_62])).

cnf(c_208,plain,
    ( r1_xboole_0(sK1,X0)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_285,plain,
    ( r1_xboole_0(sK1,X0_36)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(X0_37))
    | k3_subset_1(X0_37,X0_36) != sK2 ),
    inference(subtyping,[status(esa)],[c_208])).

cnf(c_477,plain,
    ( r1_xboole_0(sK1,k3_subset_1(X0_37,sK2))
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(X0_37,sK2),k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(X0_37))
    | k3_subset_1(X0_37,k3_subset_1(X0_37,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_483,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0_36,k1_zfmisc_1(X0_37))
    | k3_subset_1(X0_37,k3_subset_1(X0_37,X0_36)) = X0_36 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_476,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_37))
    | k3_subset_1(X0_37,k3_subset_1(X0_37,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_289])).

cnf(c_479,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_562,c_508,c_483,c_479,c_6,c_7])).


%------------------------------------------------------------------------------

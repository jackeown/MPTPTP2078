%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:34 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 131 expanded)
%              Number of clauses        :   32 (  33 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  240 ( 391 expanded)
%              Number of equality atoms :   88 ( 175 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f49])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f77,f91])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f73,f92])).

fof(f123,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f74,f92])).

fof(f121,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f103])).

fof(f122,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f121])).

fof(f15,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f15])).

fof(f25,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f51])).

fof(f90,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f52])).

fof(f108,plain,(
    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(definition_unfolding,[],[f90,f92])).

cnf(c_32,plain,
    ( r2_hidden(sK4(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1661,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_32,c_23])).

cnf(c_585,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_34532,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK4(k2_enumset1(X1,X1,X1,X1),X3))
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | X2 != X0
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_1661,c_585])).

cnf(c_34554,plain,
    ( r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | ~ r1_tarski(sK5,sK5)
    | sK5 != sK5
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_34532])).

cnf(c_31,plain,
    ( ~ r1_tarski(X0,sK4(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_6485,plain,
    ( ~ r1_tarski(X0,sK4(k2_enumset1(X1,X1,X2,X3),X0))
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))
    | k1_xboole_0 = k2_enumset1(X1,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_6489,plain,
    ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_6485])).

cnf(c_586,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1551,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_6447,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r2_hidden(X3,k1_xboole_0)
    | X3 != X0
    | k1_xboole_0 != k2_enumset1(X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_6450,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK5,k1_xboole_0)
    | sK5 != sK5
    | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_6447])).

cnf(c_27,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4548,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_30,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2884,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))))
    | m1_subset_1(sK5,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ r2_hidden(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_4547,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))))
    | ~ r2_hidden(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2884])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1698,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))))
    | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1535,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | ~ r1_tarski(X0,X3)
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X3) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_1537,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
    | ~ r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1515,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
    | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
    | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_90,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_69,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_66,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_34,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34554,c_6489,c_6450,c_4548,c_4547,c_1698,c_1537,c_1515,c_90,c_69,c_66,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:48:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.96/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/1.48  
% 7.96/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.96/1.48  
% 7.96/1.48  ------  iProver source info
% 7.96/1.48  
% 7.96/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.96/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.96/1.48  git: non_committed_changes: false
% 7.96/1.48  git: last_make_outside_of_git: false
% 7.96/1.48  
% 7.96/1.48  ------ 
% 7.96/1.48  
% 7.96/1.48  ------ Input Options
% 7.96/1.48  
% 7.96/1.48  --out_options                           all
% 7.96/1.48  --tptp_safe_out                         true
% 7.96/1.48  --problem_path                          ""
% 7.96/1.48  --include_path                          ""
% 7.96/1.48  --clausifier                            res/vclausify_rel
% 7.96/1.48  --clausifier_options                    --mode clausify
% 7.96/1.48  --stdin                                 false
% 7.96/1.48  --stats_out                             sel
% 7.96/1.48  
% 7.96/1.48  ------ General Options
% 7.96/1.48  
% 7.96/1.48  --fof                                   false
% 7.96/1.48  --time_out_real                         604.99
% 7.96/1.48  --time_out_virtual                      -1.
% 7.96/1.48  --symbol_type_check                     false
% 7.96/1.48  --clausify_out                          false
% 7.96/1.48  --sig_cnt_out                           false
% 7.96/1.48  --trig_cnt_out                          false
% 7.96/1.48  --trig_cnt_out_tolerance                1.
% 7.96/1.48  --trig_cnt_out_sk_spl                   false
% 7.96/1.48  --abstr_cl_out                          false
% 7.96/1.48  
% 7.96/1.48  ------ Global Options
% 7.96/1.48  
% 7.96/1.48  --schedule                              none
% 7.96/1.48  --add_important_lit                     false
% 7.96/1.48  --prop_solver_per_cl                    1000
% 7.96/1.48  --min_unsat_core                        false
% 7.96/1.48  --soft_assumptions                      false
% 7.96/1.48  --soft_lemma_size                       3
% 7.96/1.48  --prop_impl_unit_size                   0
% 7.96/1.48  --prop_impl_unit                        []
% 7.96/1.48  --share_sel_clauses                     true
% 7.96/1.48  --reset_solvers                         false
% 7.96/1.48  --bc_imp_inh                            [conj_cone]
% 7.96/1.48  --conj_cone_tolerance                   3.
% 7.96/1.48  --extra_neg_conj                        none
% 7.96/1.48  --large_theory_mode                     true
% 7.96/1.48  --prolific_symb_bound                   200
% 7.96/1.48  --lt_threshold                          2000
% 7.96/1.48  --clause_weak_htbl                      true
% 7.96/1.48  --gc_record_bc_elim                     false
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing Options
% 7.96/1.48  
% 7.96/1.48  --preprocessing_flag                    true
% 7.96/1.48  --time_out_prep_mult                    0.1
% 7.96/1.48  --splitting_mode                        input
% 7.96/1.48  --splitting_grd                         true
% 7.96/1.48  --splitting_cvd                         false
% 7.96/1.48  --splitting_cvd_svl                     false
% 7.96/1.48  --splitting_nvd                         32
% 7.96/1.48  --sub_typing                            true
% 7.96/1.48  --prep_gs_sim                           false
% 7.96/1.48  --prep_unflatten                        true
% 7.96/1.48  --prep_res_sim                          true
% 7.96/1.48  --prep_upred                            true
% 7.96/1.48  --prep_sem_filter                       exhaustive
% 7.96/1.48  --prep_sem_filter_out                   false
% 7.96/1.48  --pred_elim                             false
% 7.96/1.48  --res_sim_input                         true
% 7.96/1.48  --eq_ax_congr_red                       true
% 7.96/1.48  --pure_diseq_elim                       true
% 7.96/1.48  --brand_transform                       false
% 7.96/1.48  --non_eq_to_eq                          false
% 7.96/1.48  --prep_def_merge                        true
% 7.96/1.48  --prep_def_merge_prop_impl              false
% 7.96/1.48  --prep_def_merge_mbd                    true
% 7.96/1.48  --prep_def_merge_tr_red                 false
% 7.96/1.48  --prep_def_merge_tr_cl                  false
% 7.96/1.48  --smt_preprocessing                     true
% 7.96/1.48  --smt_ac_axioms                         fast
% 7.96/1.48  --preprocessed_out                      false
% 7.96/1.48  --preprocessed_stats                    false
% 7.96/1.48  
% 7.96/1.48  ------ Abstraction refinement Options
% 7.96/1.48  
% 7.96/1.48  --abstr_ref                             []
% 7.96/1.48  --abstr_ref_prep                        false
% 7.96/1.48  --abstr_ref_until_sat                   false
% 7.96/1.48  --abstr_ref_sig_restrict                funpre
% 7.96/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.96/1.48  --abstr_ref_under                       []
% 7.96/1.48  
% 7.96/1.48  ------ SAT Options
% 7.96/1.48  
% 7.96/1.48  --sat_mode                              false
% 7.96/1.48  --sat_fm_restart_options                ""
% 7.96/1.48  --sat_gr_def                            false
% 7.96/1.48  --sat_epr_types                         true
% 7.96/1.48  --sat_non_cyclic_types                  false
% 7.96/1.48  --sat_finite_models                     false
% 7.96/1.48  --sat_fm_lemmas                         false
% 7.96/1.48  --sat_fm_prep                           false
% 7.96/1.48  --sat_fm_uc_incr                        true
% 7.96/1.48  --sat_out_model                         small
% 7.96/1.48  --sat_out_clauses                       false
% 7.96/1.48  
% 7.96/1.48  ------ QBF Options
% 7.96/1.48  
% 7.96/1.48  --qbf_mode                              false
% 7.96/1.48  --qbf_elim_univ                         false
% 7.96/1.48  --qbf_dom_inst                          none
% 7.96/1.48  --qbf_dom_pre_inst                      false
% 7.96/1.48  --qbf_sk_in                             false
% 7.96/1.48  --qbf_pred_elim                         true
% 7.96/1.48  --qbf_split                             512
% 7.96/1.48  
% 7.96/1.48  ------ BMC1 Options
% 7.96/1.48  
% 7.96/1.48  --bmc1_incremental                      false
% 7.96/1.48  --bmc1_axioms                           reachable_all
% 7.96/1.48  --bmc1_min_bound                        0
% 7.96/1.48  --bmc1_max_bound                        -1
% 7.96/1.48  --bmc1_max_bound_default                -1
% 7.96/1.48  --bmc1_symbol_reachability              true
% 7.96/1.48  --bmc1_property_lemmas                  false
% 7.96/1.48  --bmc1_k_induction                      false
% 7.96/1.48  --bmc1_non_equiv_states                 false
% 7.96/1.48  --bmc1_deadlock                         false
% 7.96/1.48  --bmc1_ucm                              false
% 7.96/1.48  --bmc1_add_unsat_core                   none
% 7.96/1.48  --bmc1_unsat_core_children              false
% 7.96/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.96/1.48  --bmc1_out_stat                         full
% 7.96/1.48  --bmc1_ground_init                      false
% 7.96/1.48  --bmc1_pre_inst_next_state              false
% 7.96/1.48  --bmc1_pre_inst_state                   false
% 7.96/1.48  --bmc1_pre_inst_reach_state             false
% 7.96/1.48  --bmc1_out_unsat_core                   false
% 7.96/1.48  --bmc1_aig_witness_out                  false
% 7.96/1.48  --bmc1_verbose                          false
% 7.96/1.48  --bmc1_dump_clauses_tptp                false
% 7.96/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.96/1.48  --bmc1_dump_file                        -
% 7.96/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.96/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.96/1.48  --bmc1_ucm_extend_mode                  1
% 7.96/1.48  --bmc1_ucm_init_mode                    2
% 7.96/1.48  --bmc1_ucm_cone_mode                    none
% 7.96/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.96/1.48  --bmc1_ucm_relax_model                  4
% 7.96/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.96/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.96/1.48  --bmc1_ucm_layered_model                none
% 7.96/1.48  --bmc1_ucm_max_lemma_size               10
% 7.96/1.48  
% 7.96/1.48  ------ AIG Options
% 7.96/1.48  
% 7.96/1.48  --aig_mode                              false
% 7.96/1.48  
% 7.96/1.48  ------ Instantiation Options
% 7.96/1.48  
% 7.96/1.48  --instantiation_flag                    true
% 7.96/1.48  --inst_sos_flag                         false
% 7.96/1.48  --inst_sos_phase                        true
% 7.96/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.96/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.96/1.48  --inst_lit_sel_side                     num_symb
% 7.96/1.48  --inst_solver_per_active                1400
% 7.96/1.48  --inst_solver_calls_frac                1.
% 7.96/1.48  --inst_passive_queue_type               priority_queues
% 7.96/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.96/1.48  --inst_passive_queues_freq              [25;2]
% 7.96/1.48  --inst_dismatching                      true
% 7.96/1.48  --inst_eager_unprocessed_to_passive     true
% 7.96/1.48  --inst_prop_sim_given                   true
% 7.96/1.48  --inst_prop_sim_new                     false
% 7.96/1.48  --inst_subs_new                         false
% 7.96/1.48  --inst_eq_res_simp                      false
% 7.96/1.48  --inst_subs_given                       false
% 7.96/1.48  --inst_orphan_elimination               true
% 7.96/1.48  --inst_learning_loop_flag               true
% 7.96/1.48  --inst_learning_start                   3000
% 7.96/1.48  --inst_learning_factor                  2
% 7.96/1.48  --inst_start_prop_sim_after_learn       3
% 7.96/1.48  --inst_sel_renew                        solver
% 7.96/1.48  --inst_lit_activity_flag                true
% 7.96/1.48  --inst_restr_to_given                   false
% 7.96/1.48  --inst_activity_threshold               500
% 7.96/1.48  --inst_out_proof                        true
% 7.96/1.48  
% 7.96/1.48  ------ Resolution Options
% 7.96/1.48  
% 7.96/1.48  --resolution_flag                       true
% 7.96/1.48  --res_lit_sel                           adaptive
% 7.96/1.48  --res_lit_sel_side                      none
% 7.96/1.48  --res_ordering                          kbo
% 7.96/1.48  --res_to_prop_solver                    active
% 7.96/1.48  --res_prop_simpl_new                    false
% 7.96/1.48  --res_prop_simpl_given                  true
% 7.96/1.48  --res_passive_queue_type                priority_queues
% 7.96/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.96/1.48  --res_passive_queues_freq               [15;5]
% 7.96/1.48  --res_forward_subs                      full
% 7.96/1.48  --res_backward_subs                     full
% 7.96/1.48  --res_forward_subs_resolution           true
% 7.96/1.48  --res_backward_subs_resolution          true
% 7.96/1.48  --res_orphan_elimination                true
% 7.96/1.48  --res_time_limit                        2.
% 7.96/1.48  --res_out_proof                         true
% 7.96/1.48  
% 7.96/1.48  ------ Superposition Options
% 7.96/1.48  
% 7.96/1.48  --superposition_flag                    true
% 7.96/1.48  --sup_passive_queue_type                priority_queues
% 7.96/1.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.96/1.48  --sup_passive_queues_freq               [1;4]
% 7.96/1.48  --demod_completeness_check              fast
% 7.96/1.48  --demod_use_ground                      true
% 7.96/1.48  --sup_to_prop_solver                    passive
% 7.96/1.48  --sup_prop_simpl_new                    true
% 7.96/1.48  --sup_prop_simpl_given                  true
% 7.96/1.48  --sup_fun_splitting                     false
% 7.96/1.48  --sup_smt_interval                      50000
% 7.96/1.48  
% 7.96/1.48  ------ Superposition Simplification Setup
% 7.96/1.48  
% 7.96/1.48  --sup_indices_passive                   []
% 7.96/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.96/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.96/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.96/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.96/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.96/1.48  --sup_full_bw                           [BwDemod]
% 7.96/1.48  --sup_immed_triv                        [TrivRules]
% 7.96/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.96/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.96/1.48  --sup_immed_bw_main                     []
% 7.96/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.96/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.96/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.96/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.96/1.48  
% 7.96/1.48  ------ Combination Options
% 7.96/1.48  
% 7.96/1.48  --comb_res_mult                         3
% 7.96/1.48  --comb_sup_mult                         2
% 7.96/1.48  --comb_inst_mult                        10
% 7.96/1.48  
% 7.96/1.48  ------ Debug Options
% 7.96/1.48  
% 7.96/1.48  --dbg_backtrace                         false
% 7.96/1.48  --dbg_dump_prop_clauses                 false
% 7.96/1.48  --dbg_dump_prop_clauses_file            -
% 7.96/1.48  --dbg_out_stat                          false
% 7.96/1.48  ------ Parsing...
% 7.96/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.48  ------ Proving...
% 7.96/1.48  ------ Problem Properties 
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  clauses                                 34
% 7.96/1.48  conjectures                             1
% 7.96/1.48  EPR                                     3
% 7.96/1.48  Horn                                    23
% 7.96/1.48  unary                                   8
% 7.96/1.48  binary                                  8
% 7.96/1.48  lits                                    82
% 7.96/1.48  lits eq                                 26
% 7.96/1.48  fd_pure                                 0
% 7.96/1.48  fd_pseudo                               0
% 7.96/1.48  fd_cond                                 2
% 7.96/1.48  fd_pseudo_cond                          11
% 7.96/1.48  AC symbols                              0
% 7.96/1.48  
% 7.96/1.48  ------ Input Options Time Limit: Unbounded
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ 
% 7.96/1.48  Current options:
% 7.96/1.48  ------ 
% 7.96/1.48  
% 7.96/1.48  ------ Input Options
% 7.96/1.48  
% 7.96/1.48  --out_options                           all
% 7.96/1.48  --tptp_safe_out                         true
% 7.96/1.48  --problem_path                          ""
% 7.96/1.48  --include_path                          ""
% 7.96/1.48  --clausifier                            res/vclausify_rel
% 7.96/1.48  --clausifier_options                    --mode clausify
% 7.96/1.48  --stdin                                 false
% 7.96/1.48  --stats_out                             sel
% 7.96/1.48  
% 7.96/1.48  ------ General Options
% 7.96/1.48  
% 7.96/1.48  --fof                                   false
% 7.96/1.48  --time_out_real                         604.99
% 7.96/1.48  --time_out_virtual                      -1.
% 7.96/1.48  --symbol_type_check                     false
% 7.96/1.48  --clausify_out                          false
% 7.96/1.48  --sig_cnt_out                           false
% 7.96/1.48  --trig_cnt_out                          false
% 7.96/1.48  --trig_cnt_out_tolerance                1.
% 7.96/1.48  --trig_cnt_out_sk_spl                   false
% 7.96/1.48  --abstr_cl_out                          false
% 7.96/1.48  
% 7.96/1.48  ------ Global Options
% 7.96/1.48  
% 7.96/1.48  --schedule                              none
% 7.96/1.48  --add_important_lit                     false
% 7.96/1.48  --prop_solver_per_cl                    1000
% 7.96/1.48  --min_unsat_core                        false
% 7.96/1.48  --soft_assumptions                      false
% 7.96/1.48  --soft_lemma_size                       3
% 7.96/1.48  --prop_impl_unit_size                   0
% 7.96/1.48  --prop_impl_unit                        []
% 7.96/1.48  --share_sel_clauses                     true
% 7.96/1.48  --reset_solvers                         false
% 7.96/1.48  --bc_imp_inh                            [conj_cone]
% 7.96/1.48  --conj_cone_tolerance                   3.
% 7.96/1.48  --extra_neg_conj                        none
% 7.96/1.48  --large_theory_mode                     true
% 7.96/1.48  --prolific_symb_bound                   200
% 7.96/1.48  --lt_threshold                          2000
% 7.96/1.48  --clause_weak_htbl                      true
% 7.96/1.48  --gc_record_bc_elim                     false
% 7.96/1.48  
% 7.96/1.48  ------ Preprocessing Options
% 7.96/1.48  
% 7.96/1.48  --preprocessing_flag                    true
% 7.96/1.48  --time_out_prep_mult                    0.1
% 7.96/1.48  --splitting_mode                        input
% 7.96/1.48  --splitting_grd                         true
% 7.96/1.48  --splitting_cvd                         false
% 7.96/1.48  --splitting_cvd_svl                     false
% 7.96/1.48  --splitting_nvd                         32
% 7.96/1.48  --sub_typing                            true
% 7.96/1.48  --prep_gs_sim                           false
% 7.96/1.48  --prep_unflatten                        true
% 7.96/1.48  --prep_res_sim                          true
% 7.96/1.48  --prep_upred                            true
% 7.96/1.48  --prep_sem_filter                       exhaustive
% 7.96/1.48  --prep_sem_filter_out                   false
% 7.96/1.48  --pred_elim                             false
% 7.96/1.48  --res_sim_input                         true
% 7.96/1.48  --eq_ax_congr_red                       true
% 7.96/1.48  --pure_diseq_elim                       true
% 7.96/1.48  --brand_transform                       false
% 7.96/1.48  --non_eq_to_eq                          false
% 7.96/1.48  --prep_def_merge                        true
% 7.96/1.48  --prep_def_merge_prop_impl              false
% 7.96/1.48  --prep_def_merge_mbd                    true
% 7.96/1.48  --prep_def_merge_tr_red                 false
% 7.96/1.48  --prep_def_merge_tr_cl                  false
% 7.96/1.48  --smt_preprocessing                     true
% 7.96/1.48  --smt_ac_axioms                         fast
% 7.96/1.48  --preprocessed_out                      false
% 7.96/1.48  --preprocessed_stats                    false
% 7.96/1.48  
% 7.96/1.48  ------ Abstraction refinement Options
% 7.96/1.48  
% 7.96/1.48  --abstr_ref                             []
% 7.96/1.48  --abstr_ref_prep                        false
% 7.96/1.48  --abstr_ref_until_sat                   false
% 7.96/1.48  --abstr_ref_sig_restrict                funpre
% 7.96/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.96/1.48  --abstr_ref_under                       []
% 7.96/1.48  
% 7.96/1.48  ------ SAT Options
% 7.96/1.48  
% 7.96/1.48  --sat_mode                              false
% 7.96/1.48  --sat_fm_restart_options                ""
% 7.96/1.48  --sat_gr_def                            false
% 7.96/1.48  --sat_epr_types                         true
% 7.96/1.48  --sat_non_cyclic_types                  false
% 7.96/1.48  --sat_finite_models                     false
% 7.96/1.48  --sat_fm_lemmas                         false
% 7.96/1.48  --sat_fm_prep                           false
% 7.96/1.48  --sat_fm_uc_incr                        true
% 7.96/1.48  --sat_out_model                         small
% 7.96/1.48  --sat_out_clauses                       false
% 7.96/1.48  
% 7.96/1.48  ------ QBF Options
% 7.96/1.48  
% 7.96/1.48  --qbf_mode                              false
% 7.96/1.48  --qbf_elim_univ                         false
% 7.96/1.48  --qbf_dom_inst                          none
% 7.96/1.48  --qbf_dom_pre_inst                      false
% 7.96/1.48  --qbf_sk_in                             false
% 7.96/1.48  --qbf_pred_elim                         true
% 7.96/1.48  --qbf_split                             512
% 7.96/1.48  
% 7.96/1.48  ------ BMC1 Options
% 7.96/1.48  
% 7.96/1.48  --bmc1_incremental                      false
% 7.96/1.48  --bmc1_axioms                           reachable_all
% 7.96/1.48  --bmc1_min_bound                        0
% 7.96/1.48  --bmc1_max_bound                        -1
% 7.96/1.48  --bmc1_max_bound_default                -1
% 7.96/1.48  --bmc1_symbol_reachability              true
% 7.96/1.48  --bmc1_property_lemmas                  false
% 7.96/1.48  --bmc1_k_induction                      false
% 7.96/1.48  --bmc1_non_equiv_states                 false
% 7.96/1.48  --bmc1_deadlock                         false
% 7.96/1.48  --bmc1_ucm                              false
% 7.96/1.48  --bmc1_add_unsat_core                   none
% 7.96/1.48  --bmc1_unsat_core_children              false
% 7.96/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.96/1.48  --bmc1_out_stat                         full
% 7.96/1.48  --bmc1_ground_init                      false
% 7.96/1.48  --bmc1_pre_inst_next_state              false
% 7.96/1.48  --bmc1_pre_inst_state                   false
% 7.96/1.48  --bmc1_pre_inst_reach_state             false
% 7.96/1.48  --bmc1_out_unsat_core                   false
% 7.96/1.48  --bmc1_aig_witness_out                  false
% 7.96/1.48  --bmc1_verbose                          false
% 7.96/1.48  --bmc1_dump_clauses_tptp                false
% 7.96/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.96/1.48  --bmc1_dump_file                        -
% 7.96/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.96/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.96/1.48  --bmc1_ucm_extend_mode                  1
% 7.96/1.48  --bmc1_ucm_init_mode                    2
% 7.96/1.48  --bmc1_ucm_cone_mode                    none
% 7.96/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.96/1.48  --bmc1_ucm_relax_model                  4
% 7.96/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.96/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.96/1.48  --bmc1_ucm_layered_model                none
% 7.96/1.48  --bmc1_ucm_max_lemma_size               10
% 7.96/1.48  
% 7.96/1.48  ------ AIG Options
% 7.96/1.48  
% 7.96/1.48  --aig_mode                              false
% 7.96/1.48  
% 7.96/1.48  ------ Instantiation Options
% 7.96/1.48  
% 7.96/1.48  --instantiation_flag                    true
% 7.96/1.48  --inst_sos_flag                         false
% 7.96/1.48  --inst_sos_phase                        true
% 7.96/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.96/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.96/1.48  --inst_lit_sel_side                     num_symb
% 7.96/1.48  --inst_solver_per_active                1400
% 7.96/1.48  --inst_solver_calls_frac                1.
% 7.96/1.48  --inst_passive_queue_type               priority_queues
% 7.96/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.96/1.48  --inst_passive_queues_freq              [25;2]
% 7.96/1.48  --inst_dismatching                      true
% 7.96/1.48  --inst_eager_unprocessed_to_passive     true
% 7.96/1.48  --inst_prop_sim_given                   true
% 7.96/1.48  --inst_prop_sim_new                     false
% 7.96/1.48  --inst_subs_new                         false
% 7.96/1.48  --inst_eq_res_simp                      false
% 7.96/1.48  --inst_subs_given                       false
% 7.96/1.48  --inst_orphan_elimination               true
% 7.96/1.48  --inst_learning_loop_flag               true
% 7.96/1.48  --inst_learning_start                   3000
% 7.96/1.48  --inst_learning_factor                  2
% 7.96/1.48  --inst_start_prop_sim_after_learn       3
% 7.96/1.48  --inst_sel_renew                        solver
% 7.96/1.48  --inst_lit_activity_flag                true
% 7.96/1.48  --inst_restr_to_given                   false
% 7.96/1.48  --inst_activity_threshold               500
% 7.96/1.48  --inst_out_proof                        true
% 7.96/1.48  
% 7.96/1.48  ------ Resolution Options
% 7.96/1.48  
% 7.96/1.48  --resolution_flag                       true
% 7.96/1.48  --res_lit_sel                           adaptive
% 7.96/1.48  --res_lit_sel_side                      none
% 7.96/1.48  --res_ordering                          kbo
% 7.96/1.48  --res_to_prop_solver                    active
% 7.96/1.48  --res_prop_simpl_new                    false
% 7.96/1.48  --res_prop_simpl_given                  true
% 7.96/1.48  --res_passive_queue_type                priority_queues
% 7.96/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.96/1.48  --res_passive_queues_freq               [15;5]
% 7.96/1.48  --res_forward_subs                      full
% 7.96/1.48  --res_backward_subs                     full
% 7.96/1.48  --res_forward_subs_resolution           true
% 7.96/1.48  --res_backward_subs_resolution          true
% 7.96/1.48  --res_orphan_elimination                true
% 7.96/1.48  --res_time_limit                        2.
% 7.96/1.48  --res_out_proof                         true
% 7.96/1.48  
% 7.96/1.48  ------ Superposition Options
% 7.96/1.48  
% 7.96/1.48  --superposition_flag                    true
% 7.96/1.48  --sup_passive_queue_type                priority_queues
% 7.96/1.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.96/1.48  --sup_passive_queues_freq               [1;4]
% 7.96/1.48  --demod_completeness_check              fast
% 7.96/1.48  --demod_use_ground                      true
% 7.96/1.48  --sup_to_prop_solver                    passive
% 7.96/1.48  --sup_prop_simpl_new                    true
% 7.96/1.48  --sup_prop_simpl_given                  true
% 7.96/1.48  --sup_fun_splitting                     false
% 7.96/1.48  --sup_smt_interval                      50000
% 7.96/1.48  
% 7.96/1.48  ------ Superposition Simplification Setup
% 7.96/1.48  
% 7.96/1.48  --sup_indices_passive                   []
% 7.96/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.96/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.96/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.96/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.96/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.96/1.48  --sup_full_bw                           [BwDemod]
% 7.96/1.48  --sup_immed_triv                        [TrivRules]
% 7.96/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.96/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.96/1.48  --sup_immed_bw_main                     []
% 7.96/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.96/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.96/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.96/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.96/1.48  
% 7.96/1.48  ------ Combination Options
% 7.96/1.48  
% 7.96/1.48  --comb_res_mult                         3
% 7.96/1.48  --comb_sup_mult                         2
% 7.96/1.48  --comb_inst_mult                        10
% 7.96/1.48  
% 7.96/1.48  ------ Debug Options
% 7.96/1.48  
% 7.96/1.48  --dbg_backtrace                         false
% 7.96/1.48  --dbg_dump_prop_clauses                 false
% 7.96/1.48  --dbg_dump_prop_clauses_file            -
% 7.96/1.48  --dbg_out_stat                          false
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  ------ Proving...
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  % SZS status Theorem for theBenchmark.p
% 7.96/1.48  
% 7.96/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.96/1.48  
% 7.96/1.48  fof(f13,axiom,(
% 7.96/1.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f21,plain,(
% 7.96/1.48    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 7.96/1.48    inference(ennf_transformation,[],[f13])).
% 7.96/1.48  
% 7.96/1.48  fof(f22,plain,(
% 7.96/1.48    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 7.96/1.48    inference(flattening,[],[f21])).
% 7.96/1.48  
% 7.96/1.48  fof(f49,plain,(
% 7.96/1.48    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 7.96/1.48    introduced(choice_axiom,[])).
% 7.96/1.48  
% 7.96/1.48  fof(f50,plain,(
% 7.96/1.48    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),X0)))),
% 7.96/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f49])).
% 7.96/1.48  
% 7.96/1.48  fof(f87,plain,(
% 7.96/1.48    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK4(X0,X1),X0)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f50])).
% 7.96/1.48  
% 7.96/1.48  fof(f5,axiom,(
% 7.96/1.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f42,plain,(
% 7.96/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.96/1.48    inference(nnf_transformation,[],[f5])).
% 7.96/1.48  
% 7.96/1.48  fof(f43,plain,(
% 7.96/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.96/1.48    inference(rectify,[],[f42])).
% 7.96/1.48  
% 7.96/1.48  fof(f44,plain,(
% 7.96/1.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 7.96/1.48    introduced(choice_axiom,[])).
% 7.96/1.48  
% 7.96/1.48  fof(f45,plain,(
% 7.96/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.96/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 7.96/1.48  
% 7.96/1.48  fof(f73,plain,(
% 7.96/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.96/1.48    inference(cnf_transformation,[],[f45])).
% 7.96/1.48  
% 7.96/1.48  fof(f6,axiom,(
% 7.96/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f77,plain,(
% 7.96/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f6])).
% 7.96/1.48  
% 7.96/1.48  fof(f7,axiom,(
% 7.96/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f78,plain,(
% 7.96/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f7])).
% 7.96/1.48  
% 7.96/1.48  fof(f8,axiom,(
% 7.96/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f79,plain,(
% 7.96/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f8])).
% 7.96/1.48  
% 7.96/1.48  fof(f91,plain,(
% 7.96/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.96/1.48    inference(definition_unfolding,[],[f78,f79])).
% 7.96/1.48  
% 7.96/1.48  fof(f92,plain,(
% 7.96/1.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.96/1.48    inference(definition_unfolding,[],[f77,f91])).
% 7.96/1.48  
% 7.96/1.48  fof(f104,plain,(
% 7.96/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.96/1.48    inference(definition_unfolding,[],[f73,f92])).
% 7.96/1.48  
% 7.96/1.48  fof(f123,plain,(
% 7.96/1.48    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.96/1.48    inference(equality_resolution,[],[f104])).
% 7.96/1.48  
% 7.96/1.48  fof(f88,plain,(
% 7.96/1.48    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK4(X0,X1))) )),
% 7.96/1.48    inference(cnf_transformation,[],[f50])).
% 7.96/1.48  
% 7.96/1.48  fof(f10,axiom,(
% 7.96/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f83,plain,(
% 7.96/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.96/1.48    inference(cnf_transformation,[],[f10])).
% 7.96/1.48  
% 7.96/1.48  fof(f12,axiom,(
% 7.96/1.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f19,plain,(
% 7.96/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.96/1.48    inference(ennf_transformation,[],[f12])).
% 7.96/1.48  
% 7.96/1.48  fof(f20,plain,(
% 7.96/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.96/1.48    inference(flattening,[],[f19])).
% 7.96/1.48  
% 7.96/1.48  fof(f86,plain,(
% 7.96/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f20])).
% 7.96/1.48  
% 7.96/1.48  fof(f11,axiom,(
% 7.96/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f48,plain,(
% 7.96/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.96/1.48    inference(nnf_transformation,[],[f11])).
% 7.96/1.48  
% 7.96/1.48  fof(f84,plain,(
% 7.96/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.96/1.48    inference(cnf_transformation,[],[f48])).
% 7.96/1.48  
% 7.96/1.48  fof(f14,axiom,(
% 7.96/1.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f23,plain,(
% 7.96/1.48    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 7.96/1.48    inference(ennf_transformation,[],[f14])).
% 7.96/1.48  
% 7.96/1.48  fof(f24,plain,(
% 7.96/1.48    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 7.96/1.48    inference(flattening,[],[f23])).
% 7.96/1.48  
% 7.96/1.48  fof(f89,plain,(
% 7.96/1.48    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f24])).
% 7.96/1.48  
% 7.96/1.48  fof(f3,axiom,(
% 7.96/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f35,plain,(
% 7.96/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.96/1.48    inference(nnf_transformation,[],[f3])).
% 7.96/1.48  
% 7.96/1.48  fof(f36,plain,(
% 7.96/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.96/1.48    inference(flattening,[],[f35])).
% 7.96/1.48  
% 7.96/1.48  fof(f64,plain,(
% 7.96/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.96/1.48    inference(cnf_transformation,[],[f36])).
% 7.96/1.48  
% 7.96/1.48  fof(f62,plain,(
% 7.96/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.96/1.48    inference(cnf_transformation,[],[f36])).
% 7.96/1.48  
% 7.96/1.48  fof(f113,plain,(
% 7.96/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.96/1.48    inference(equality_resolution,[],[f62])).
% 7.96/1.48  
% 7.96/1.48  fof(f74,plain,(
% 7.96/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.96/1.48    inference(cnf_transformation,[],[f45])).
% 7.96/1.48  
% 7.96/1.48  fof(f103,plain,(
% 7.96/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.96/1.48    inference(definition_unfolding,[],[f74,f92])).
% 7.96/1.48  
% 7.96/1.48  fof(f121,plain,(
% 7.96/1.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 7.96/1.48    inference(equality_resolution,[],[f103])).
% 7.96/1.48  
% 7.96/1.48  fof(f122,plain,(
% 7.96/1.48    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 7.96/1.48    inference(equality_resolution,[],[f121])).
% 7.96/1.48  
% 7.96/1.48  fof(f15,conjecture,(
% 7.96/1.48    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.96/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.48  
% 7.96/1.48  fof(f16,negated_conjecture,(
% 7.96/1.48    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 7.96/1.48    inference(negated_conjecture,[],[f15])).
% 7.96/1.48  
% 7.96/1.48  fof(f25,plain,(
% 7.96/1.48    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 7.96/1.48    inference(ennf_transformation,[],[f16])).
% 7.96/1.48  
% 7.96/1.48  fof(f51,plain,(
% 7.96/1.48    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK5)) != sK5),
% 7.96/1.48    introduced(choice_axiom,[])).
% 7.96/1.48  
% 7.96/1.48  fof(f52,plain,(
% 7.96/1.48    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 7.96/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f51])).
% 7.96/1.48  
% 7.96/1.48  fof(f90,plain,(
% 7.96/1.48    k1_setfam_1(k1_tarski(sK5)) != sK5),
% 7.96/1.48    inference(cnf_transformation,[],[f52])).
% 7.96/1.48  
% 7.96/1.48  fof(f108,plain,(
% 7.96/1.48    k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5),
% 7.96/1.48    inference(definition_unfolding,[],[f90,f92])).
% 7.96/1.48  
% 7.96/1.48  cnf(c_32,plain,
% 7.96/1.48      ( r2_hidden(sK4(X0,X1),X0)
% 7.96/1.48      | r1_tarski(X1,k1_setfam_1(X0))
% 7.96/1.48      | k1_xboole_0 = X0 ),
% 7.96/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_23,plain,
% 7.96/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.96/1.48      inference(cnf_transformation,[],[f123]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_1661,plain,
% 7.96/1.48      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 7.96/1.48      | sK4(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 7.96/1.48      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 7.96/1.48      inference(resolution,[status(thm)],[c_32,c_23]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_585,plain,
% 7.96/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.96/1.48      theory(equality) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34532,plain,
% 7.96/1.48      ( ~ r1_tarski(X0,X1)
% 7.96/1.48      | r1_tarski(X2,sK4(k2_enumset1(X1,X1,X1,X1),X3))
% 7.96/1.48      | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 7.96/1.48      | X2 != X0
% 7.96/1.48      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 7.96/1.48      inference(resolution,[status(thm)],[c_1661,c_585]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34554,plain,
% 7.96/1.48      ( r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 7.96/1.48      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.96/1.48      | ~ r1_tarski(sK5,sK5)
% 7.96/1.48      | sK5 != sK5
% 7.96/1.48      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_34532]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_31,plain,
% 7.96/1.48      ( ~ r1_tarski(X0,sK4(X1,X0))
% 7.96/1.48      | r1_tarski(X0,k1_setfam_1(X1))
% 7.96/1.48      | k1_xboole_0 = X1 ),
% 7.96/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_6485,plain,
% 7.96/1.48      ( ~ r1_tarski(X0,sK4(k2_enumset1(X1,X1,X2,X3),X0))
% 7.96/1.48      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X2,X3)))
% 7.96/1.48      | k1_xboole_0 = k2_enumset1(X1,X1,X2,X3) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_31]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_6489,plain,
% 7.96/1.48      ( ~ r1_tarski(sK5,sK4(k2_enumset1(sK5,sK5,sK5,sK5),sK5))
% 7.96/1.48      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.96/1.48      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_6485]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_586,plain,
% 7.96/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.96/1.48      theory(equality) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_1551,plain,
% 7.96/1.48      ( r2_hidden(X0,X1)
% 7.96/1.48      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 7.96/1.48      | X0 != X2
% 7.96/1.48      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_586]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_6447,plain,
% 7.96/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 7.96/1.48      | r2_hidden(X3,k1_xboole_0)
% 7.96/1.48      | X3 != X0
% 7.96/1.48      | k1_xboole_0 != k2_enumset1(X1,X1,X2,X0) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_1551]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_6450,plain,
% 7.96/1.48      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.96/1.48      | r2_hidden(sK5,k1_xboole_0)
% 7.96/1.48      | sK5 != sK5
% 7.96/1.48      | k1_xboole_0 != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_6447]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_27,plain,
% 7.96/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.96/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_4548,plain,
% 7.96/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))))) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_27]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_30,plain,
% 7.96/1.48      ( m1_subset_1(X0,X1)
% 7.96/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.96/1.48      | ~ r2_hidden(X0,X2) ),
% 7.96/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_2884,plain,
% 7.96/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))))
% 7.96/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))))
% 7.96/1.48      | ~ r2_hidden(sK5,X0) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_30]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_4547,plain,
% 7.96/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))))
% 7.96/1.48      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))))
% 7.96/1.48      | ~ r2_hidden(sK5,k1_xboole_0) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_2884]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_29,plain,
% 7.96/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.96/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_1698,plain,
% 7.96/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))))
% 7.96/1.48      | r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_29]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_33,plain,
% 7.96/1.48      ( ~ r2_hidden(X0,X1)
% 7.96/1.48      | ~ r1_tarski(X0,X2)
% 7.96/1.48      | r1_tarski(k1_setfam_1(X1),X2) ),
% 7.96/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_1535,plain,
% 7.96/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 7.96/1.48      | ~ r1_tarski(X0,X3)
% 7.96/1.48      | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X0)),X3) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_33]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_1537,plain,
% 7.96/1.48      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.96/1.48      | r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
% 7.96/1.48      | ~ r1_tarski(sK5,sK5) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_1535]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_9,plain,
% 7.96/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.96/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_1515,plain,
% 7.96/1.48      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)),sK5)
% 7.96/1.48      | ~ r1_tarski(sK5,k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)))
% 7.96/1.48      | k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) = sK5 ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_11,plain,
% 7.96/1.48      ( r1_tarski(X0,X0) ),
% 7.96/1.48      inference(cnf_transformation,[],[f113]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_90,plain,
% 7.96/1.48      ( r1_tarski(sK5,sK5) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_22,plain,
% 7.96/1.48      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 7.96/1.48      inference(cnf_transformation,[],[f122]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_69,plain,
% 7.96/1.48      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_66,plain,
% 7.96/1.48      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 7.96/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(c_34,negated_conjecture,
% 7.96/1.48      ( k1_setfam_1(k2_enumset1(sK5,sK5,sK5,sK5)) != sK5 ),
% 7.96/1.48      inference(cnf_transformation,[],[f108]) ).
% 7.96/1.48  
% 7.96/1.48  cnf(contradiction,plain,
% 7.96/1.48      ( $false ),
% 7.96/1.48      inference(minisat,
% 7.96/1.48                [status(thm)],
% 7.96/1.48                [c_34554,c_6489,c_6450,c_4548,c_4547,c_1698,c_1537,
% 7.96/1.48                 c_1515,c_90,c_69,c_66,c_34]) ).
% 7.96/1.48  
% 7.96/1.48  
% 7.96/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.96/1.48  
% 7.96/1.48  ------                               Statistics
% 7.96/1.48  
% 7.96/1.48  ------ Selected
% 7.96/1.48  
% 7.96/1.48  total_time:                             0.994
% 7.96/1.48  
%------------------------------------------------------------------------------

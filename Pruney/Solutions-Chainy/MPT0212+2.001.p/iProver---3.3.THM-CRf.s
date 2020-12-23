%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:36 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   69 (  97 expanded)
%              Number of clauses        :   29 (  29 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  218 ( 390 expanded)
%              Number of equality atoms :  107 ( 194 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f71,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f60])).

fof(f72,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f73,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f8,conjecture,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(flattening,[],[f9])).

fof(f57,plain,(
    k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f57,f52])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6242,plain,
    ( ~ r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_518,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3218,plain,
    ( sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_519,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1892,plain,
    ( sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != X0
    | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_3217,plain,
    ( sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 != sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | k2_enumset1(X0,X0,X0,X0) = X1
    | sK2(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1029,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK2(X0,X1) = X0
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1023,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2187,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_zfmisc_1(X1)
    | sK2(X0,k1_zfmisc_1(X1)) = X0
    | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1029,c_1023])).

cnf(c_2218,plain,
    ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
    | k2_enumset1(X0,X0,X0,X0) = k1_zfmisc_1(X1)
    | sK2(X0,k1_zfmisc_1(X1)) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2187])).

cnf(c_2220,plain,
    ( r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2218])).

cnf(c_521,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1433,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_1435,plain,
    ( r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1433])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1303,plain,
    ( ~ r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | k2_enumset1(X0,X0,X0,X0) = X1
    | sK2(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1235,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_53,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_41,plain,
    ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_24,negated_conjecture,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6242,c_3218,c_3217,c_2220,c_1435,c_1303,c_1235,c_53,c_41,c_38,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:30:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.21/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/0.97  
% 2.21/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/0.97  
% 2.21/0.97  ------  iProver source info
% 2.21/0.97  
% 2.21/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.21/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/0.97  git: non_committed_changes: false
% 2.21/0.97  git: last_make_outside_of_git: false
% 2.21/0.97  
% 2.21/0.97  ------ 
% 2.21/0.97  
% 2.21/0.97  ------ Input Options
% 2.21/0.97  
% 2.21/0.97  --out_options                           all
% 2.21/0.97  --tptp_safe_out                         true
% 2.21/0.97  --problem_path                          ""
% 2.21/0.97  --include_path                          ""
% 2.21/0.97  --clausifier                            res/vclausify_rel
% 2.21/0.97  --clausifier_options                    --mode clausify
% 2.21/0.97  --stdin                                 false
% 2.21/0.97  --stats_out                             all
% 2.21/0.97  
% 2.21/0.97  ------ General Options
% 2.21/0.97  
% 2.21/0.97  --fof                                   false
% 2.21/0.97  --time_out_real                         305.
% 2.21/0.97  --time_out_virtual                      -1.
% 2.21/0.97  --symbol_type_check                     false
% 2.21/0.97  --clausify_out                          false
% 2.21/0.97  --sig_cnt_out                           false
% 2.21/0.97  --trig_cnt_out                          false
% 2.21/0.97  --trig_cnt_out_tolerance                1.
% 2.21/0.97  --trig_cnt_out_sk_spl                   false
% 2.21/0.97  --abstr_cl_out                          false
% 2.21/0.97  
% 2.21/0.97  ------ Global Options
% 2.21/0.97  
% 2.21/0.97  --schedule                              default
% 2.21/0.97  --add_important_lit                     false
% 2.21/0.97  --prop_solver_per_cl                    1000
% 2.21/0.97  --min_unsat_core                        false
% 2.21/0.97  --soft_assumptions                      false
% 2.21/0.97  --soft_lemma_size                       3
% 2.21/0.97  --prop_impl_unit_size                   0
% 2.21/0.97  --prop_impl_unit                        []
% 2.21/0.97  --share_sel_clauses                     true
% 2.21/0.97  --reset_solvers                         false
% 2.21/0.97  --bc_imp_inh                            [conj_cone]
% 2.21/0.97  --conj_cone_tolerance                   3.
% 2.21/0.97  --extra_neg_conj                        none
% 2.21/0.97  --large_theory_mode                     true
% 2.21/0.97  --prolific_symb_bound                   200
% 2.21/0.97  --lt_threshold                          2000
% 2.21/0.97  --clause_weak_htbl                      true
% 2.21/0.97  --gc_record_bc_elim                     false
% 2.21/0.97  
% 2.21/0.97  ------ Preprocessing Options
% 2.21/0.97  
% 2.21/0.97  --preprocessing_flag                    true
% 2.21/0.97  --time_out_prep_mult                    0.1
% 2.21/0.97  --splitting_mode                        input
% 2.21/0.97  --splitting_grd                         true
% 2.21/0.97  --splitting_cvd                         false
% 2.21/0.97  --splitting_cvd_svl                     false
% 2.21/0.97  --splitting_nvd                         32
% 2.21/0.97  --sub_typing                            true
% 2.21/0.97  --prep_gs_sim                           true
% 2.21/0.97  --prep_unflatten                        true
% 2.21/0.97  --prep_res_sim                          true
% 2.21/0.97  --prep_upred                            true
% 2.21/0.97  --prep_sem_filter                       exhaustive
% 2.21/0.97  --prep_sem_filter_out                   false
% 2.21/0.97  --pred_elim                             true
% 2.21/0.97  --res_sim_input                         true
% 2.21/0.97  --eq_ax_congr_red                       true
% 2.21/0.97  --pure_diseq_elim                       true
% 2.21/0.97  --brand_transform                       false
% 2.21/0.97  --non_eq_to_eq                          false
% 2.21/0.97  --prep_def_merge                        true
% 2.21/0.97  --prep_def_merge_prop_impl              false
% 2.21/0.97  --prep_def_merge_mbd                    true
% 2.21/0.97  --prep_def_merge_tr_red                 false
% 2.21/0.97  --prep_def_merge_tr_cl                  false
% 2.21/0.97  --smt_preprocessing                     true
% 2.21/0.97  --smt_ac_axioms                         fast
% 2.21/0.97  --preprocessed_out                      false
% 2.21/0.97  --preprocessed_stats                    false
% 2.21/0.97  
% 2.21/0.97  ------ Abstraction refinement Options
% 2.21/0.97  
% 2.21/0.97  --abstr_ref                             []
% 2.21/0.97  --abstr_ref_prep                        false
% 2.21/0.97  --abstr_ref_until_sat                   false
% 2.21/0.97  --abstr_ref_sig_restrict                funpre
% 2.21/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/0.97  --abstr_ref_under                       []
% 2.21/0.97  
% 2.21/0.97  ------ SAT Options
% 2.21/0.97  
% 2.21/0.97  --sat_mode                              false
% 2.21/0.97  --sat_fm_restart_options                ""
% 2.21/0.97  --sat_gr_def                            false
% 2.21/0.97  --sat_epr_types                         true
% 2.21/0.97  --sat_non_cyclic_types                  false
% 2.21/0.97  --sat_finite_models                     false
% 2.21/0.97  --sat_fm_lemmas                         false
% 2.21/0.97  --sat_fm_prep                           false
% 2.21/0.97  --sat_fm_uc_incr                        true
% 2.21/0.97  --sat_out_model                         small
% 2.21/0.97  --sat_out_clauses                       false
% 2.21/0.97  
% 2.21/0.97  ------ QBF Options
% 2.21/0.97  
% 2.21/0.97  --qbf_mode                              false
% 2.21/0.97  --qbf_elim_univ                         false
% 2.21/0.97  --qbf_dom_inst                          none
% 2.21/0.97  --qbf_dom_pre_inst                      false
% 2.21/0.97  --qbf_sk_in                             false
% 2.21/0.97  --qbf_pred_elim                         true
% 2.21/0.97  --qbf_split                             512
% 2.21/0.97  
% 2.21/0.97  ------ BMC1 Options
% 2.21/0.97  
% 2.21/0.97  --bmc1_incremental                      false
% 2.21/0.97  --bmc1_axioms                           reachable_all
% 2.21/0.97  --bmc1_min_bound                        0
% 2.21/0.97  --bmc1_max_bound                        -1
% 2.21/0.97  --bmc1_max_bound_default                -1
% 2.21/0.97  --bmc1_symbol_reachability              true
% 2.21/0.97  --bmc1_property_lemmas                  false
% 2.21/0.97  --bmc1_k_induction                      false
% 2.21/0.97  --bmc1_non_equiv_states                 false
% 2.21/0.97  --bmc1_deadlock                         false
% 2.21/0.97  --bmc1_ucm                              false
% 2.21/0.97  --bmc1_add_unsat_core                   none
% 2.21/0.97  --bmc1_unsat_core_children              false
% 2.21/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/0.97  --bmc1_out_stat                         full
% 2.21/0.97  --bmc1_ground_init                      false
% 2.21/0.97  --bmc1_pre_inst_next_state              false
% 2.21/0.97  --bmc1_pre_inst_state                   false
% 2.21/0.97  --bmc1_pre_inst_reach_state             false
% 2.21/0.97  --bmc1_out_unsat_core                   false
% 2.21/0.97  --bmc1_aig_witness_out                  false
% 2.21/0.97  --bmc1_verbose                          false
% 2.21/0.97  --bmc1_dump_clauses_tptp                false
% 2.21/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.21/0.97  --bmc1_dump_file                        -
% 2.21/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.21/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.21/0.97  --bmc1_ucm_extend_mode                  1
% 2.21/0.97  --bmc1_ucm_init_mode                    2
% 2.21/0.97  --bmc1_ucm_cone_mode                    none
% 2.21/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.21/0.97  --bmc1_ucm_relax_model                  4
% 2.21/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.21/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/0.97  --bmc1_ucm_layered_model                none
% 2.21/0.97  --bmc1_ucm_max_lemma_size               10
% 2.21/0.97  
% 2.21/0.97  ------ AIG Options
% 2.21/0.97  
% 2.21/0.97  --aig_mode                              false
% 2.21/0.97  
% 2.21/0.97  ------ Instantiation Options
% 2.21/0.97  
% 2.21/0.97  --instantiation_flag                    true
% 2.21/0.97  --inst_sos_flag                         false
% 2.21/0.97  --inst_sos_phase                        true
% 2.21/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/0.97  --inst_lit_sel_side                     num_symb
% 2.21/0.97  --inst_solver_per_active                1400
% 2.21/0.97  --inst_solver_calls_frac                1.
% 2.21/0.97  --inst_passive_queue_type               priority_queues
% 2.21/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/0.97  --inst_passive_queues_freq              [25;2]
% 2.21/0.97  --inst_dismatching                      true
% 2.21/0.97  --inst_eager_unprocessed_to_passive     true
% 2.21/0.97  --inst_prop_sim_given                   true
% 2.21/0.97  --inst_prop_sim_new                     false
% 2.21/0.97  --inst_subs_new                         false
% 2.21/0.97  --inst_eq_res_simp                      false
% 2.21/0.97  --inst_subs_given                       false
% 2.21/0.97  --inst_orphan_elimination               true
% 2.21/0.97  --inst_learning_loop_flag               true
% 2.21/0.97  --inst_learning_start                   3000
% 2.21/0.97  --inst_learning_factor                  2
% 2.21/0.97  --inst_start_prop_sim_after_learn       3
% 2.21/0.97  --inst_sel_renew                        solver
% 2.21/0.97  --inst_lit_activity_flag                true
% 2.21/0.97  --inst_restr_to_given                   false
% 2.21/0.97  --inst_activity_threshold               500
% 2.21/0.97  --inst_out_proof                        true
% 2.21/0.97  
% 2.21/0.97  ------ Resolution Options
% 2.21/0.97  
% 2.21/0.97  --resolution_flag                       true
% 2.21/0.97  --res_lit_sel                           adaptive
% 2.21/0.97  --res_lit_sel_side                      none
% 2.21/0.97  --res_ordering                          kbo
% 2.21/0.97  --res_to_prop_solver                    active
% 2.21/0.97  --res_prop_simpl_new                    false
% 2.21/0.97  --res_prop_simpl_given                  true
% 2.21/0.97  --res_passive_queue_type                priority_queues
% 2.21/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/0.97  --res_passive_queues_freq               [15;5]
% 2.21/0.97  --res_forward_subs                      full
% 2.21/0.97  --res_backward_subs                     full
% 2.21/0.97  --res_forward_subs_resolution           true
% 2.21/0.97  --res_backward_subs_resolution          true
% 2.21/0.97  --res_orphan_elimination                true
% 2.21/0.97  --res_time_limit                        2.
% 2.21/0.97  --res_out_proof                         true
% 2.21/0.97  
% 2.21/0.97  ------ Superposition Options
% 2.21/0.97  
% 2.21/0.97  --superposition_flag                    true
% 2.21/0.97  --sup_passive_queue_type                priority_queues
% 2.21/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.21/0.97  --demod_completeness_check              fast
% 2.21/0.97  --demod_use_ground                      true
% 2.21/0.97  --sup_to_prop_solver                    passive
% 2.21/0.97  --sup_prop_simpl_new                    true
% 2.21/0.97  --sup_prop_simpl_given                  true
% 2.21/0.97  --sup_fun_splitting                     false
% 2.21/0.97  --sup_smt_interval                      50000
% 2.21/0.97  
% 2.21/0.97  ------ Superposition Simplification Setup
% 2.21/0.97  
% 2.21/0.97  --sup_indices_passive                   []
% 2.21/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.97  --sup_full_bw                           [BwDemod]
% 2.21/0.97  --sup_immed_triv                        [TrivRules]
% 2.21/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.97  --sup_immed_bw_main                     []
% 2.21/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.97  
% 2.21/0.97  ------ Combination Options
% 2.21/0.97  
% 2.21/0.97  --comb_res_mult                         3
% 2.21/0.97  --comb_sup_mult                         2
% 2.21/0.97  --comb_inst_mult                        10
% 2.21/0.97  
% 2.21/0.97  ------ Debug Options
% 2.21/0.97  
% 2.21/0.97  --dbg_backtrace                         false
% 2.21/0.97  --dbg_dump_prop_clauses                 false
% 2.21/0.97  --dbg_dump_prop_clauses_file            -
% 2.21/0.97  --dbg_out_stat                          false
% 2.21/0.97  ------ Parsing...
% 2.21/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/0.97  
% 2.21/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.21/0.97  
% 2.21/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/0.97  
% 2.21/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/0.97  ------ Proving...
% 2.21/0.97  ------ Problem Properties 
% 2.21/0.97  
% 2.21/0.97  
% 2.21/0.97  clauses                                 24
% 2.21/0.97  conjectures                             1
% 2.21/0.97  EPR                                     3
% 2.21/0.97  Horn                                    16
% 2.21/0.97  unary                                   3
% 2.21/0.97  binary                                  8
% 2.21/0.97  lits                                    60
% 2.21/0.97  lits eq                                 16
% 2.21/0.97  fd_pure                                 0
% 2.21/0.97  fd_pseudo                               0
% 2.21/0.97  fd_cond                                 1
% 2.21/0.97  fd_pseudo_cond                          11
% 2.21/0.97  AC symbols                              0
% 2.21/0.97  
% 2.21/0.97  ------ Schedule dynamic 5 is on 
% 2.21/0.97  
% 2.21/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/0.97  
% 2.21/0.97  
% 2.21/0.97  ------ 
% 2.21/0.97  Current options:
% 2.21/0.97  ------ 
% 2.21/0.97  
% 2.21/0.97  ------ Input Options
% 2.21/0.97  
% 2.21/0.97  --out_options                           all
% 2.21/0.97  --tptp_safe_out                         true
% 2.21/0.97  --problem_path                          ""
% 2.21/0.97  --include_path                          ""
% 2.21/0.97  --clausifier                            res/vclausify_rel
% 2.21/0.97  --clausifier_options                    --mode clausify
% 2.21/0.97  --stdin                                 false
% 2.21/0.97  --stats_out                             all
% 2.21/0.97  
% 2.21/0.97  ------ General Options
% 2.21/0.97  
% 2.21/0.97  --fof                                   false
% 2.21/0.97  --time_out_real                         305.
% 2.21/0.97  --time_out_virtual                      -1.
% 2.21/0.97  --symbol_type_check                     false
% 2.21/0.97  --clausify_out                          false
% 2.21/0.97  --sig_cnt_out                           false
% 2.21/0.97  --trig_cnt_out                          false
% 2.21/0.97  --trig_cnt_out_tolerance                1.
% 2.21/0.97  --trig_cnt_out_sk_spl                   false
% 2.21/0.97  --abstr_cl_out                          false
% 2.21/0.97  
% 2.21/0.97  ------ Global Options
% 2.21/0.97  
% 2.21/0.97  --schedule                              default
% 2.21/0.97  --add_important_lit                     false
% 2.21/0.97  --prop_solver_per_cl                    1000
% 2.21/0.97  --min_unsat_core                        false
% 2.21/0.97  --soft_assumptions                      false
% 2.21/0.97  --soft_lemma_size                       3
% 2.21/0.97  --prop_impl_unit_size                   0
% 2.21/0.97  --prop_impl_unit                        []
% 2.21/0.97  --share_sel_clauses                     true
% 2.21/0.97  --reset_solvers                         false
% 2.21/0.97  --bc_imp_inh                            [conj_cone]
% 2.21/0.97  --conj_cone_tolerance                   3.
% 2.21/0.97  --extra_neg_conj                        none
% 2.21/0.97  --large_theory_mode                     true
% 2.21/0.97  --prolific_symb_bound                   200
% 2.21/0.97  --lt_threshold                          2000
% 2.21/0.97  --clause_weak_htbl                      true
% 2.21/0.97  --gc_record_bc_elim                     false
% 2.21/0.97  
% 2.21/0.97  ------ Preprocessing Options
% 2.21/0.97  
% 2.21/0.97  --preprocessing_flag                    true
% 2.21/0.97  --time_out_prep_mult                    0.1
% 2.21/0.97  --splitting_mode                        input
% 2.21/0.97  --splitting_grd                         true
% 2.21/0.97  --splitting_cvd                         false
% 2.21/0.97  --splitting_cvd_svl                     false
% 2.21/0.97  --splitting_nvd                         32
% 2.21/0.97  --sub_typing                            true
% 2.21/0.97  --prep_gs_sim                           true
% 2.21/0.97  --prep_unflatten                        true
% 2.21/0.97  --prep_res_sim                          true
% 2.21/0.97  --prep_upred                            true
% 2.21/0.97  --prep_sem_filter                       exhaustive
% 2.21/0.97  --prep_sem_filter_out                   false
% 2.21/0.97  --pred_elim                             true
% 2.21/0.97  --res_sim_input                         true
% 2.21/0.97  --eq_ax_congr_red                       true
% 2.21/0.97  --pure_diseq_elim                       true
% 2.21/0.97  --brand_transform                       false
% 2.21/0.97  --non_eq_to_eq                          false
% 2.21/0.97  --prep_def_merge                        true
% 2.21/0.97  --prep_def_merge_prop_impl              false
% 2.21/0.97  --prep_def_merge_mbd                    true
% 2.21/0.97  --prep_def_merge_tr_red                 false
% 2.21/0.97  --prep_def_merge_tr_cl                  false
% 2.21/0.97  --smt_preprocessing                     true
% 2.21/0.97  --smt_ac_axioms                         fast
% 2.21/0.97  --preprocessed_out                      false
% 2.21/0.97  --preprocessed_stats                    false
% 2.21/0.97  
% 2.21/0.97  ------ Abstraction refinement Options
% 2.21/0.97  
% 2.21/0.97  --abstr_ref                             []
% 2.21/0.97  --abstr_ref_prep                        false
% 2.21/0.97  --abstr_ref_until_sat                   false
% 2.21/0.97  --abstr_ref_sig_restrict                funpre
% 2.21/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/0.97  --abstr_ref_under                       []
% 2.21/0.97  
% 2.21/0.97  ------ SAT Options
% 2.21/0.97  
% 2.21/0.97  --sat_mode                              false
% 2.21/0.97  --sat_fm_restart_options                ""
% 2.21/0.97  --sat_gr_def                            false
% 2.21/0.97  --sat_epr_types                         true
% 2.21/0.97  --sat_non_cyclic_types                  false
% 2.21/0.97  --sat_finite_models                     false
% 2.21/0.97  --sat_fm_lemmas                         false
% 2.21/0.97  --sat_fm_prep                           false
% 2.21/0.97  --sat_fm_uc_incr                        true
% 2.21/0.97  --sat_out_model                         small
% 2.21/0.97  --sat_out_clauses                       false
% 2.21/0.97  
% 2.21/0.97  ------ QBF Options
% 2.21/0.97  
% 2.21/0.97  --qbf_mode                              false
% 2.21/0.97  --qbf_elim_univ                         false
% 2.21/0.97  --qbf_dom_inst                          none
% 2.21/0.97  --qbf_dom_pre_inst                      false
% 2.21/0.97  --qbf_sk_in                             false
% 2.21/0.97  --qbf_pred_elim                         true
% 2.21/0.97  --qbf_split                             512
% 2.21/0.97  
% 2.21/0.97  ------ BMC1 Options
% 2.21/0.97  
% 2.21/0.97  --bmc1_incremental                      false
% 2.21/0.97  --bmc1_axioms                           reachable_all
% 2.21/0.97  --bmc1_min_bound                        0
% 2.21/0.97  --bmc1_max_bound                        -1
% 2.21/0.97  --bmc1_max_bound_default                -1
% 2.21/0.97  --bmc1_symbol_reachability              true
% 2.21/0.97  --bmc1_property_lemmas                  false
% 2.21/0.97  --bmc1_k_induction                      false
% 2.21/0.97  --bmc1_non_equiv_states                 false
% 2.21/0.97  --bmc1_deadlock                         false
% 2.21/0.97  --bmc1_ucm                              false
% 2.21/0.97  --bmc1_add_unsat_core                   none
% 2.21/0.97  --bmc1_unsat_core_children              false
% 2.21/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/0.97  --bmc1_out_stat                         full
% 2.21/0.97  --bmc1_ground_init                      false
% 2.21/0.97  --bmc1_pre_inst_next_state              false
% 2.21/0.97  --bmc1_pre_inst_state                   false
% 2.21/0.97  --bmc1_pre_inst_reach_state             false
% 2.21/0.97  --bmc1_out_unsat_core                   false
% 2.21/0.97  --bmc1_aig_witness_out                  false
% 2.21/0.97  --bmc1_verbose                          false
% 2.21/0.97  --bmc1_dump_clauses_tptp                false
% 2.21/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.21/0.97  --bmc1_dump_file                        -
% 2.21/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.21/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.21/0.97  --bmc1_ucm_extend_mode                  1
% 2.21/0.97  --bmc1_ucm_init_mode                    2
% 2.21/0.97  --bmc1_ucm_cone_mode                    none
% 2.21/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.21/0.97  --bmc1_ucm_relax_model                  4
% 2.21/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.21/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/0.97  --bmc1_ucm_layered_model                none
% 2.21/0.97  --bmc1_ucm_max_lemma_size               10
% 2.21/0.97  
% 2.21/0.97  ------ AIG Options
% 2.21/0.97  
% 2.21/0.97  --aig_mode                              false
% 2.21/0.97  
% 2.21/0.97  ------ Instantiation Options
% 2.21/0.97  
% 2.21/0.97  --instantiation_flag                    true
% 2.21/0.97  --inst_sos_flag                         false
% 2.21/0.97  --inst_sos_phase                        true
% 2.21/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/0.97  --inst_lit_sel_side                     none
% 2.21/0.97  --inst_solver_per_active                1400
% 2.21/0.97  --inst_solver_calls_frac                1.
% 2.21/0.97  --inst_passive_queue_type               priority_queues
% 2.21/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/0.97  --inst_passive_queues_freq              [25;2]
% 2.21/0.97  --inst_dismatching                      true
% 2.21/0.97  --inst_eager_unprocessed_to_passive     true
% 2.21/0.97  --inst_prop_sim_given                   true
% 2.21/0.97  --inst_prop_sim_new                     false
% 2.21/0.97  --inst_subs_new                         false
% 2.21/0.97  --inst_eq_res_simp                      false
% 2.21/0.97  --inst_subs_given                       false
% 2.21/0.97  --inst_orphan_elimination               true
% 2.21/0.97  --inst_learning_loop_flag               true
% 2.21/0.97  --inst_learning_start                   3000
% 2.21/0.97  --inst_learning_factor                  2
% 2.21/0.97  --inst_start_prop_sim_after_learn       3
% 2.21/0.97  --inst_sel_renew                        solver
% 2.21/0.97  --inst_lit_activity_flag                true
% 2.21/0.97  --inst_restr_to_given                   false
% 2.21/0.97  --inst_activity_threshold               500
% 2.21/0.97  --inst_out_proof                        true
% 2.21/0.97  
% 2.21/0.97  ------ Resolution Options
% 2.21/0.97  
% 2.21/0.97  --resolution_flag                       false
% 2.21/0.97  --res_lit_sel                           adaptive
% 2.21/0.97  --res_lit_sel_side                      none
% 2.21/0.97  --res_ordering                          kbo
% 2.21/0.97  --res_to_prop_solver                    active
% 2.21/0.97  --res_prop_simpl_new                    false
% 2.21/0.97  --res_prop_simpl_given                  true
% 2.21/0.97  --res_passive_queue_type                priority_queues
% 2.21/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/0.97  --res_passive_queues_freq               [15;5]
% 2.21/0.97  --res_forward_subs                      full
% 2.21/0.97  --res_backward_subs                     full
% 2.21/0.97  --res_forward_subs_resolution           true
% 2.21/0.97  --res_backward_subs_resolution          true
% 2.21/0.97  --res_orphan_elimination                true
% 2.21/0.97  --res_time_limit                        2.
% 2.21/0.97  --res_out_proof                         true
% 2.21/0.97  
% 2.21/0.97  ------ Superposition Options
% 2.21/0.97  
% 2.21/0.97  --superposition_flag                    true
% 2.21/0.97  --sup_passive_queue_type                priority_queues
% 2.21/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.21/0.97  --demod_completeness_check              fast
% 2.21/0.97  --demod_use_ground                      true
% 2.21/0.97  --sup_to_prop_solver                    passive
% 2.21/0.97  --sup_prop_simpl_new                    true
% 2.21/0.97  --sup_prop_simpl_given                  true
% 2.21/0.97  --sup_fun_splitting                     false
% 2.21/0.97  --sup_smt_interval                      50000
% 2.21/0.97  
% 2.21/0.97  ------ Superposition Simplification Setup
% 2.21/0.97  
% 2.21/0.97  --sup_indices_passive                   []
% 2.21/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.97  --sup_full_bw                           [BwDemod]
% 2.21/0.97  --sup_immed_triv                        [TrivRules]
% 2.21/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.97  --sup_immed_bw_main                     []
% 2.21/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.97  
% 2.21/0.97  ------ Combination Options
% 2.21/0.97  
% 2.21/0.97  --comb_res_mult                         3
% 2.21/0.97  --comb_sup_mult                         2
% 2.21/0.97  --comb_inst_mult                        10
% 2.21/0.97  
% 2.21/0.97  ------ Debug Options
% 2.21/0.97  
% 2.21/0.97  --dbg_backtrace                         false
% 2.21/0.97  --dbg_dump_prop_clauses                 false
% 2.21/0.97  --dbg_dump_prop_clauses_file            -
% 2.21/0.97  --dbg_out_stat                          false
% 2.21/0.97  
% 2.21/0.97  
% 2.21/0.97  
% 2.21/0.97  
% 2.21/0.97  ------ Proving...
% 2.21/0.97  
% 2.21/0.97  
% 2.21/0.97  % SZS status Theorem for theBenchmark.p
% 2.21/0.97  
% 2.21/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/0.97  
% 2.21/0.97  fof(f4,axiom,(
% 2.21/0.97    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.21/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.97  
% 2.21/0.97  fof(f11,plain,(
% 2.21/0.97    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.21/0.97    inference(ennf_transformation,[],[f4])).
% 2.21/0.97  
% 2.21/0.97  fof(f47,plain,(
% 2.21/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.21/0.97    inference(cnf_transformation,[],[f11])).
% 2.21/0.97  
% 2.21/0.97  fof(f5,axiom,(
% 2.21/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.21/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.97  
% 2.21/0.97  fof(f24,plain,(
% 2.21/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.21/0.97    inference(nnf_transformation,[],[f5])).
% 2.21/0.97  
% 2.21/0.97  fof(f25,plain,(
% 2.21/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.21/0.97    inference(rectify,[],[f24])).
% 2.21/0.97  
% 2.21/0.97  fof(f26,plain,(
% 2.21/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.21/0.97    introduced(choice_axiom,[])).
% 2.21/0.97  
% 2.21/0.97  fof(f27,plain,(
% 2.21/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.21/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 2.21/0.97  
% 2.21/0.97  fof(f50,plain,(
% 2.21/0.97    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 2.21/0.97    inference(cnf_transformation,[],[f27])).
% 2.21/0.97  
% 2.21/0.97  fof(f6,axiom,(
% 2.21/0.97    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 2.21/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.97  
% 2.21/0.97  fof(f52,plain,(
% 2.21/0.97    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.21/0.97    inference(cnf_transformation,[],[f6])).
% 2.21/0.97  
% 2.21/0.97  fof(f59,plain,(
% 2.21/0.97    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 2.21/0.97    inference(definition_unfolding,[],[f50,f52])).
% 2.21/0.97  
% 2.21/0.97  fof(f7,axiom,(
% 2.21/0.97    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.21/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.97  
% 2.21/0.97  fof(f28,plain,(
% 2.21/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.21/0.97    inference(nnf_transformation,[],[f7])).
% 2.21/0.97  
% 2.21/0.97  fof(f29,plain,(
% 2.21/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.21/0.97    inference(rectify,[],[f28])).
% 2.21/0.97  
% 2.21/0.97  fof(f30,plain,(
% 2.21/0.97    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.21/0.97    introduced(choice_axiom,[])).
% 2.21/0.97  
% 2.21/0.97  fof(f31,plain,(
% 2.21/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.21/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 2.21/0.97  
% 2.21/0.97  fof(f53,plain,(
% 2.21/0.97    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.21/0.97    inference(cnf_transformation,[],[f31])).
% 2.21/0.97  
% 2.21/0.97  fof(f75,plain,(
% 2.21/0.97    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.21/0.97    inference(equality_resolution,[],[f53])).
% 2.21/0.97  
% 2.21/0.97  fof(f54,plain,(
% 2.21/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.21/0.97    inference(cnf_transformation,[],[f31])).
% 2.21/0.97  
% 2.21/0.97  fof(f74,plain,(
% 2.21/0.97    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.21/0.97    inference(equality_resolution,[],[f54])).
% 2.21/0.97  
% 2.21/0.97  fof(f51,plain,(
% 2.21/0.97    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.21/0.97    inference(cnf_transformation,[],[f27])).
% 2.21/0.97  
% 2.21/0.97  fof(f58,plain,(
% 2.21/0.97    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.21/0.97    inference(definition_unfolding,[],[f51,f52])).
% 2.21/0.97  
% 2.21/0.97  fof(f3,axiom,(
% 2.21/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.97  
% 2.21/0.97  fof(f22,plain,(
% 2.21/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.97    inference(nnf_transformation,[],[f3])).
% 2.21/0.97  
% 2.21/0.97  fof(f23,plain,(
% 2.21/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.97    inference(flattening,[],[f22])).
% 2.21/0.97  
% 2.21/0.97  fof(f44,plain,(
% 2.21/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.21/0.97    inference(cnf_transformation,[],[f23])).
% 2.21/0.97  
% 2.21/0.97  fof(f70,plain,(
% 2.21/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.21/0.97    inference(equality_resolution,[],[f44])).
% 2.21/0.97  
% 2.21/0.97  fof(f49,plain,(
% 2.21/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.21/0.97    inference(cnf_transformation,[],[f27])).
% 2.21/0.97  
% 2.21/0.97  fof(f60,plain,(
% 2.21/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.21/0.97    inference(definition_unfolding,[],[f49,f52])).
% 2.21/0.97  
% 2.21/0.97  fof(f71,plain,(
% 2.21/0.97    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 2.21/0.97    inference(equality_resolution,[],[f60])).
% 2.21/0.97  
% 2.21/0.97  fof(f72,plain,(
% 2.21/0.97    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 2.21/0.97    inference(equality_resolution,[],[f71])).
% 2.21/0.97  
% 2.21/0.97  fof(f48,plain,(
% 2.21/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.21/0.97    inference(cnf_transformation,[],[f27])).
% 2.21/0.97  
% 2.21/0.97  fof(f61,plain,(
% 2.21/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.21/0.97    inference(definition_unfolding,[],[f48,f52])).
% 2.21/0.97  
% 2.21/0.97  fof(f73,plain,(
% 2.21/0.97    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 2.21/0.97    inference(equality_resolution,[],[f61])).
% 2.21/0.97  
% 2.21/0.97  fof(f8,conjecture,(
% 2.21/0.97    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 2.21/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.97  
% 2.21/0.97  fof(f9,negated_conjecture,(
% 2.21/0.97    ~k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 2.21/0.97    inference(negated_conjecture,[],[f8])).
% 2.21/0.97  
% 2.21/0.97  fof(f10,plain,(
% 2.21/0.97    k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)),
% 2.21/0.97    inference(flattening,[],[f9])).
% 2.21/0.97  
% 2.21/0.97  fof(f57,plain,(
% 2.21/0.97    k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)),
% 2.21/0.97    inference(cnf_transformation,[],[f10])).
% 2.21/0.97  
% 2.21/0.97  fof(f62,plain,(
% 2.21/0.97    k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)),
% 2.21/0.97    inference(definition_unfolding,[],[f57,f52])).
% 2.21/0.97  
% 2.21/0.97  cnf(c_15,plain,
% 2.21/0.97      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.21/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_6242,plain,
% 2.21/0.97      ( ~ r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
% 2.21/0.97      | k1_xboole_0 = sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_15]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_518,plain,( X0 = X0 ),theory(equality) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_3218,plain,
% 2.21/0.97      ( sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_518]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_519,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_1892,plain,
% 2.21/0.97      ( sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != X0
% 2.21/0.97      | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 2.21/0.97      | k1_xboole_0 != X0 ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_519]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_3217,plain,
% 2.21/0.97      ( sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.21/0.97      | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 2.21/0.97      | k1_xboole_0 != sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_1892]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_17,plain,
% 2.21/0.97      ( r2_hidden(sK2(X0,X1),X1)
% 2.21/0.97      | k2_enumset1(X0,X0,X0,X0) = X1
% 2.21/0.97      | sK2(X0,X1) = X0 ),
% 2.21/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_1029,plain,
% 2.21/0.97      ( k2_enumset1(X0,X0,X0,X0) = X1
% 2.21/0.97      | sK2(X0,X1) = X0
% 2.21/0.97      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 2.21/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_23,plain,
% 2.21/0.97      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.21/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_1023,plain,
% 2.21/0.97      ( r1_tarski(X0,X1) = iProver_top
% 2.21/0.97      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.21/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_2187,plain,
% 2.21/0.97      ( k2_enumset1(X0,X0,X0,X0) = k1_zfmisc_1(X1)
% 2.21/0.97      | sK2(X0,k1_zfmisc_1(X1)) = X0
% 2.21/0.97      | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
% 2.21/0.97      inference(superposition,[status(thm)],[c_1029,c_1023]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_2218,plain,
% 2.21/0.97      ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
% 2.21/0.97      | k2_enumset1(X0,X0,X0,X0) = k1_zfmisc_1(X1)
% 2.21/0.97      | sK2(X0,k1_zfmisc_1(X1)) = X0 ),
% 2.21/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2187]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_2220,plain,
% 2.21/0.97      ( r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
% 2.21/0.97      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 2.21/0.97      | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_2218]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_521,plain,
% 2.21/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.21/0.97      theory(equality) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_1433,plain,
% 2.21/0.97      ( ~ r1_tarski(X0,X1)
% 2.21/0.97      | r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
% 2.21/0.97      | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != X0
% 2.21/0.97      | k1_xboole_0 != X1 ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_521]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_1435,plain,
% 2.21/0.97      ( r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
% 2.21/0.97      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.21/0.97      | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
% 2.21/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_1433]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_22,plain,
% 2.21/0.97      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.21/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_1303,plain,
% 2.21/0.97      ( ~ r1_tarski(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
% 2.21/0.97      | r2_hidden(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_22]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_16,plain,
% 2.21/0.97      ( ~ r2_hidden(sK2(X0,X1),X1)
% 2.21/0.97      | k2_enumset1(X0,X0,X0,X0) = X1
% 2.21/0.97      | sK2(X0,X1) != X0 ),
% 2.21/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_1235,plain,
% 2.21/0.97      ( ~ r2_hidden(sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
% 2.21/0.97      | k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 2.21/0.97      | sK2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0 ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_16]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_14,plain,
% 2.21/0.97      ( r1_tarski(X0,X0) ),
% 2.21/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_53,plain,
% 2.21/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_18,plain,
% 2.21/0.97      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 2.21/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_41,plain,
% 2.21/0.97      ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_18]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_19,plain,
% 2.21/0.97      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 2.21/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_38,plain,
% 2.21/0.97      ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 2.21/0.97      | k1_xboole_0 = k1_xboole_0 ),
% 2.21/0.97      inference(instantiation,[status(thm)],[c_19]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(c_24,negated_conjecture,
% 2.21/0.97      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 2.21/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.21/0.97  
% 2.21/0.97  cnf(contradiction,plain,
% 2.21/0.97      ( $false ),
% 2.21/0.97      inference(minisat,
% 2.21/0.97                [status(thm)],
% 2.21/0.97                [c_6242,c_3218,c_3217,c_2220,c_1435,c_1303,c_1235,c_53,
% 2.21/0.97                 c_41,c_38,c_24]) ).
% 2.21/0.97  
% 2.21/0.97  
% 2.21/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/0.97  
% 2.21/0.97  ------                               Statistics
% 2.21/0.97  
% 2.21/0.97  ------ General
% 2.21/0.97  
% 2.21/0.97  abstr_ref_over_cycles:                  0
% 2.21/0.97  abstr_ref_under_cycles:                 0
% 2.21/0.97  gc_basic_clause_elim:                   0
% 2.21/0.97  forced_gc_time:                         0
% 2.21/0.97  parsing_time:                           0.011
% 2.21/0.97  unif_index_cands_time:                  0.
% 2.21/0.97  unif_index_add_time:                    0.
% 2.21/0.97  orderings_time:                         0.
% 2.21/0.97  out_proof_time:                         0.007
% 2.21/0.97  total_time:                             0.196
% 2.21/0.97  num_of_symbols:                         42
% 2.21/0.97  num_of_terms:                           7480
% 2.21/0.97  
% 2.21/0.97  ------ Preprocessing
% 2.21/0.97  
% 2.21/0.97  num_of_splits:                          0
% 2.21/0.97  num_of_split_atoms:                     0
% 2.21/0.97  num_of_reused_defs:                     0
% 2.21/0.97  num_eq_ax_congr_red:                    42
% 2.21/0.97  num_of_sem_filtered_clauses:            1
% 2.21/0.97  num_of_subtypes:                        0
% 2.21/0.97  monotx_restored_types:                  0
% 2.21/0.97  sat_num_of_epr_types:                   0
% 2.21/0.97  sat_num_of_non_cyclic_types:            0
% 2.21/0.97  sat_guarded_non_collapsed_types:        0
% 2.21/0.97  num_pure_diseq_elim:                    0
% 2.21/0.97  simp_replaced_by:                       0
% 2.21/0.97  res_preprocessed:                       109
% 2.21/0.97  prep_upred:                             0
% 2.21/0.97  prep_unflattend:                        0
% 2.21/0.97  smt_new_axioms:                         0
% 2.21/0.97  pred_elim_cands:                        2
% 2.21/0.97  pred_elim:                              0
% 2.21/0.97  pred_elim_cl:                           0
% 2.21/0.97  pred_elim_cycles:                       2
% 2.21/0.97  merged_defs:                            8
% 2.21/0.97  merged_defs_ncl:                        0
% 2.21/0.97  bin_hyper_res:                          8
% 2.21/0.97  prep_cycles:                            4
% 2.21/0.97  pred_elim_time:                         0.001
% 2.21/0.97  splitting_time:                         0.
% 2.21/0.97  sem_filter_time:                        0.
% 2.21/0.97  monotx_time:                            0.
% 2.21/0.97  subtype_inf_time:                       0.
% 2.21/0.97  
% 2.21/0.97  ------ Problem properties
% 2.21/0.97  
% 2.21/0.97  clauses:                                24
% 2.21/0.97  conjectures:                            1
% 2.21/0.97  epr:                                    3
% 2.21/0.97  horn:                                   16
% 2.21/0.97  ground:                                 1
% 2.21/0.97  unary:                                  3
% 2.21/0.97  binary:                                 8
% 2.21/0.97  lits:                                   60
% 2.21/0.97  lits_eq:                                16
% 2.21/0.97  fd_pure:                                0
% 2.21/0.97  fd_pseudo:                              0
% 2.21/0.97  fd_cond:                                1
% 2.21/0.97  fd_pseudo_cond:                         11
% 2.21/0.97  ac_symbols:                             0
% 2.21/0.97  
% 2.21/0.97  ------ Propositional Solver
% 2.21/0.97  
% 2.21/0.97  prop_solver_calls:                      27
% 2.21/0.97  prop_fast_solver_calls:                 685
% 2.21/0.97  smt_solver_calls:                       0
% 2.21/0.97  smt_fast_solver_calls:                  0
% 2.21/0.97  prop_num_of_clauses:                    2327
% 2.21/0.97  prop_preprocess_simplified:             7529
% 2.21/0.97  prop_fo_subsumed:                       0
% 2.21/0.97  prop_solver_time:                       0.
% 2.21/0.97  smt_solver_time:                        0.
% 2.21/0.97  smt_fast_solver_time:                   0.
% 2.21/0.97  prop_fast_solver_time:                  0.
% 2.21/0.97  prop_unsat_core_time:                   0.
% 2.21/0.97  
% 2.21/0.97  ------ QBF
% 2.21/0.97  
% 2.21/0.97  qbf_q_res:                              0
% 2.21/0.97  qbf_num_tautologies:                    0
% 2.21/0.97  qbf_prep_cycles:                        0
% 2.21/0.97  
% 2.21/0.97  ------ BMC1
% 2.21/0.97  
% 2.21/0.97  bmc1_current_bound:                     -1
% 2.21/0.97  bmc1_last_solved_bound:                 -1
% 2.21/0.97  bmc1_unsat_core_size:                   -1
% 2.21/0.97  bmc1_unsat_core_parents_size:           -1
% 2.21/0.97  bmc1_merge_next_fun:                    0
% 2.21/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.21/0.97  
% 2.21/0.97  ------ Instantiation
% 2.21/0.97  
% 2.21/0.97  inst_num_of_clauses:                    582
% 2.21/0.97  inst_num_in_passive:                    353
% 2.21/0.97  inst_num_in_active:                     195
% 2.21/0.97  inst_num_in_unprocessed:                35
% 2.21/0.97  inst_num_of_loops:                      265
% 2.21/0.97  inst_num_of_learning_restarts:          0
% 2.21/0.97  inst_num_moves_active_passive:          68
% 2.21/0.97  inst_lit_activity:                      0
% 2.21/0.97  inst_lit_activity_moves:                0
% 2.21/0.97  inst_num_tautologies:                   0
% 2.21/0.97  inst_num_prop_implied:                  0
% 2.21/0.97  inst_num_existing_simplified:           0
% 2.21/0.97  inst_num_eq_res_simplified:             0
% 2.21/0.97  inst_num_child_elim:                    0
% 2.21/0.97  inst_num_of_dismatching_blockings:      171
% 2.21/0.97  inst_num_of_non_proper_insts:           454
% 2.21/0.97  inst_num_of_duplicates:                 0
% 2.21/0.97  inst_inst_num_from_inst_to_res:         0
% 2.21/0.97  inst_dismatching_checking_time:         0.
% 2.21/0.97  
% 2.21/0.97  ------ Resolution
% 2.21/0.97  
% 2.21/0.97  res_num_of_clauses:                     0
% 2.21/0.97  res_num_in_passive:                     0
% 2.21/0.97  res_num_in_active:                      0
% 2.21/0.97  res_num_of_loops:                       113
% 2.21/0.97  res_forward_subset_subsumed:            36
% 2.21/0.97  res_backward_subset_subsumed:           6
% 2.21/0.97  res_forward_subsumed:                   0
% 2.21/0.97  res_backward_subsumed:                  0
% 2.21/0.97  res_forward_subsumption_resolution:     0
% 2.21/0.97  res_backward_subsumption_resolution:    0
% 2.21/0.97  res_clause_to_clause_subsumption:       965
% 2.21/0.97  res_orphan_elimination:                 0
% 2.21/0.97  res_tautology_del:                      22
% 2.21/0.97  res_num_eq_res_simplified:              0
% 2.21/0.97  res_num_sel_changes:                    0
% 2.21/0.97  res_moves_from_active_to_pass:          0
% 2.21/0.97  
% 2.21/0.97  ------ Superposition
% 2.21/0.97  
% 2.21/0.97  sup_time_total:                         0.
% 2.21/0.97  sup_time_generating:                    0.
% 2.21/0.97  sup_time_sim_full:                      0.
% 2.21/0.97  sup_time_sim_immed:                     0.
% 2.21/0.97  
% 2.21/0.97  sup_num_of_clauses:                     166
% 2.21/0.97  sup_num_in_active:                      52
% 2.21/0.97  sup_num_in_passive:                     114
% 2.21/0.97  sup_num_of_loops:                       52
% 2.21/0.97  sup_fw_superposition:                   89
% 2.21/0.97  sup_bw_superposition:                   129
% 2.21/0.97  sup_immediate_simplified:               35
% 2.21/0.97  sup_given_eliminated:                   0
% 2.21/0.97  comparisons_done:                       0
% 2.21/0.97  comparisons_avoided:                    7
% 2.21/0.97  
% 2.21/0.97  ------ Simplifications
% 2.21/0.97  
% 2.21/0.97  
% 2.21/0.97  sim_fw_subset_subsumed:                 7
% 2.21/0.97  sim_bw_subset_subsumed:                 0
% 2.21/0.97  sim_fw_subsumed:                        25
% 2.21/0.97  sim_bw_subsumed:                        2
% 2.21/0.97  sim_fw_subsumption_res:                 4
% 2.21/0.97  sim_bw_subsumption_res:                 0
% 2.21/0.97  sim_tautology_del:                      18
% 2.21/0.97  sim_eq_tautology_del:                   8
% 2.21/0.97  sim_eq_res_simp:                        7
% 2.21/0.97  sim_fw_demodulated:                     0
% 2.21/0.97  sim_bw_demodulated:                     0
% 2.21/0.97  sim_light_normalised:                   0
% 2.21/0.97  sim_joinable_taut:                      0
% 2.21/0.97  sim_joinable_simp:                      0
% 2.21/0.97  sim_ac_normalised:                      0
% 2.21/0.97  sim_smt_subsumption:                    0
% 2.21/0.97  
%------------------------------------------------------------------------------

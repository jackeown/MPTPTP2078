%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0383+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:10 EST 2020

% Result     : Theorem 0.89s
% Output     : CNFRefutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   51 (  94 expanded)
%              Number of clauses        :   29 (  35 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  171 ( 377 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( ! [X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) )
   => ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != sK5
              | ~ m1_subset_1(X5,sK3) )
          | ~ m1_subset_1(X4,sK2) )
      & r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
      & r2_hidden(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ! [X4] :
        ( ! [X5] :
            ( k4_tarski(X4,X5) != sK5
            | ~ m1_subset_1(X5,sK3) )
        | ~ m1_subset_1(X4,sK2) )
    & r1_tarski(sK4,k2_zfmisc_1(sK2,sK3))
    & r2_hidden(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f9,f13])).

fof(f25,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK5
      | ~ m1_subset_1(X5,sK3)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK0(X1,X2,X3),sK1(X1,X2,X3)) = X3
        & r2_hidden(sK1(X1,X2,X3),X2)
        & r2_hidden(sK0(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK0(X1,X2,X3),sK1(X1,X2,X3)) = X3
        & r2_hidden(sK1(X1,X2,X3),X2)
        & r2_hidden(sK0(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK0(X1,X2,X3),sK1(X1,X2,X3)) = X3
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK0(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_8,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(X1,sK3)
    | k4_tarski(X0,X1) != sK5 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),sK2)
    | k4_tarski(sK0(sK2,sK3,sK5),X0) != sK5 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_714,plain,
    ( ~ m1_subset_1(sK1(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK0(sK2,sK3,sK5),sK2)
    | k4_tarski(sK0(sK2,sK3,sK5),sK1(sK2,sK3,sK5)) != sK5 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_69,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_7])).

cnf(c_70,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(renaming,[status(thm)],[c_69])).

cnf(c_643,plain,
    ( ~ r2_hidden(sK1(sK2,sK3,sK5),sK3)
    | m1_subset_1(sK1(sK2,sK3,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X0)
    | k4_tarski(sK0(X1,X2,X3),sK1(X1,X2,X3)) = X3 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_161,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_zfmisc_1(X2,X3) != k2_zfmisc_1(sK2,sK3)
    | k4_tarski(sK0(X2,X3,X0),sK1(X2,X3,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_162,plain,
    ( ~ r2_hidden(X0,sK4)
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(sK2,sK3)
    | k4_tarski(sK0(X1,X2,X0),sK1(X1,X2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_161])).

cnf(c_534,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK2,sK3)
    | k4_tarski(sK0(X0,X1,sK5),sK1(X0,X1,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_608,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(sK2,sK3)
    | k4_tarski(sK0(sK2,sK3,sK5),sK1(sK2,sK3,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK1(X1,X2,X3),X2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_146,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X2,X3,X0),X3)
    | k2_zfmisc_1(X2,X3) != k2_zfmisc_1(sK2,sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_147,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK1(X1,X2,X0),X2)
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_529,plain,
    ( r2_hidden(sK1(X0,X1,sK5),X1)
    | ~ r2_hidden(sK5,sK4)
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_609,plain,
    ( r2_hidden(sK1(sK2,sK3,sK5),sK3)
    | ~ r2_hidden(sK5,sK4)
    | k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_601,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,sK5),sK2)
    | m1_subset_1(sK0(sK2,sK3,sK5),sK2) ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_258,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_568,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK0(X1,X2,X3),X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_131,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2,X3,X0),X2)
    | k2_zfmisc_1(X2,X3) != k2_zfmisc_1(sK2,sK3)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_132,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK0(X1,X2,X0),X1)
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_131])).

cnf(c_524,plain,
    ( r2_hidden(sK0(X0,X1,sK5),X0)
    | ~ r2_hidden(sK5,sK4)
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_567,plain,
    ( r2_hidden(sK0(sK2,sK3,sK5),sK2)
    | ~ r2_hidden(sK5,sK4)
    | k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_714,c_643,c_608,c_609,c_601,c_568,c_567,c_10])).


%------------------------------------------------------------------------------

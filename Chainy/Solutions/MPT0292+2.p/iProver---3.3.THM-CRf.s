%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0292+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:34 EST 2020

% Result     : Theorem 10.87s
% Output     : CNFRefutation 10.87s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 195 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f621,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f622,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f621])).

fof(f794,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f622])).

fof(f390,conjecture,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f391,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f390])).

fof(f568,plain,(
    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f391])).

fof(f724,plain,
    ( ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0
   => k3_tarski(k1_zfmisc_1(sK37)) != sK37 ),
    introduced(choice_axiom,[])).

fof(f725,plain,(
    k3_tarski(k1_zfmisc_1(sK37)) != sK37 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK37])],[f568,f724])).

fof(f1268,plain,(
    k3_tarski(k1_zfmisc_1(sK37)) != sK37 ),
    inference(cnf_transformation,[],[f725])).

fof(f385,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f565,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f385])).

fof(f720,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK35(X0,X1),X1)
        & r2_hidden(sK35(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f721,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK35(X0,X1),X1)
        & r2_hidden(sK35(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35])],[f565,f720])).

fof(f1261,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK35(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f721])).

fof(f284,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f666,plain,(
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
    inference(nnf_transformation,[],[f284])).

fof(f667,plain,(
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
    inference(rectify,[],[f666])).

fof(f668,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK24(X0,X1),X0)
          | ~ r2_hidden(sK24(X0,X1),X1) )
        & ( r1_tarski(sK24(X0,X1),X0)
          | r2_hidden(sK24(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f669,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK24(X0,X1),X0)
            | ~ r2_hidden(sK24(X0,X1),X1) )
          & ( r1_tarski(sK24(X0,X1),X0)
            | r2_hidden(sK24(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f667,f668])).

fof(f1095,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f669])).

fof(f1680,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f1095])).

fof(f1262,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK35(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f721])).

fof(f383,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f564,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f383])).

fof(f1259,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f564])).

fof(f1096,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f669])).

fof(f1679,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f1096])).

fof(f793,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f622])).

fof(f1639,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f793])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f794])).

cnf(c_530,negated_conjecture,
    ( k3_tarski(k1_zfmisc_1(sK37)) != sK37 ),
    inference(cnf_transformation,[],[f1268])).

cnf(c_22008,plain,
    ( ~ r1_tarski(k3_tarski(k1_zfmisc_1(sK37)),sK37)
    | ~ r1_tarski(sK37,k3_tarski(k1_zfmisc_1(sK37))) ),
    inference(resolution,[status(thm)],[c_67,c_530])).

cnf(c_524,plain,
    ( r1_tarski(k3_tarski(X0),X1)
    | r2_hidden(sK35(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1261])).

cnf(c_360,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1680])).

cnf(c_19309,plain,
    ( r1_tarski(sK35(k1_zfmisc_1(X0),X1),X0)
    | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1) ),
    inference(resolution,[status(thm)],[c_524,c_360])).

cnf(c_523,plain,
    ( ~ r1_tarski(sK35(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f1262])).

cnf(c_21755,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[status(thm)],[c_19309,c_523])).

cnf(c_22015,plain,
    ( ~ r1_tarski(sK37,k3_tarski(k1_zfmisc_1(sK37))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22008,c_21755])).

cnf(c_521,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1259])).

cnf(c_22394,plain,
    ( ~ r2_hidden(sK37,k1_zfmisc_1(sK37)) ),
    inference(resolution,[status(thm)],[c_22015,c_521])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1679])).

cnf(c_22400,plain,
    ( ~ r1_tarski(sK37,sK37) ),
    inference(resolution,[status(thm)],[c_22394,c_359])).

cnf(c_68,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f1639])).

cnf(c_22529,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22400,c_68])).

%------------------------------------------------------------------------------

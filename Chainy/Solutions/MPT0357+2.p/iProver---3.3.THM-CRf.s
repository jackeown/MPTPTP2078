%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0357+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 19.87s
% Output     : CNFRefutation 19.87s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  172 ( 302 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f519,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f806,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f519])).

fof(f807,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f806])).

fof(f808,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f809,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f807,f808])).

fof(f1043,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f809])).

fof(f1044,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f809])).

fof(f497,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f788,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f497])).

fof(f789,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f788])).

fof(f1758,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f789])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f556,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f557,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f556])).

fof(f1153,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f557])).

fof(f461,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f750,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f461])).

fof(f1706,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f750])).

fof(f493,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f784,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f493])).

fof(f1024,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f784])).

fof(f1754,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1024])).

fof(f498,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f499,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f498])).

fof(f790,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f499])).

fof(f791,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f790])).

fof(f1026,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,sK73),X1)
        & r1_tarski(k3_subset_1(X0,X1),sK73)
        & m1_subset_1(sK73,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1025,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK71,X2),sK72)
          & r1_tarski(k3_subset_1(sK71,sK72),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK71)) )
      & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ) ),
    introduced(choice_axiom,[])).

fof(f1027,plain,
    ( ~ r1_tarski(k3_subset_1(sK71,sK73),sK72)
    & r1_tarski(k3_subset_1(sK71,sK72),sK73)
    & m1_subset_1(sK73,k1_zfmisc_1(sK71))
    & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK71,sK72,sK73])],[f791,f1026,f1025])).

fof(f1762,plain,(
    ~ r1_tarski(k3_subset_1(sK71,sK73),sK72) ),
    inference(cnf_transformation,[],[f1027])).

fof(f1761,plain,(
    r1_tarski(k3_subset_1(sK71,sK72),sK73) ),
    inference(cnf_transformation,[],[f1027])).

fof(f1760,plain,(
    m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1027])).

fof(f1759,plain,(
    m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1027])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1043])).

cnf(c_43729,plain,
    ( r1_tarski(k3_subset_1(sK71,sK73),X0)
    | r2_hidden(sK5(k3_subset_1(sK71,sK73),X0),k3_subset_1(sK71,sK73)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_62236,plain,
    ( r1_tarski(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK73))
    | r2_hidden(sK5(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK73)),k3_subset_1(sK71,sK73)) ),
    inference(instantiation,[status(thm)],[c_43729])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1044])).

cnf(c_43727,plain,
    ( r1_tarski(k3_subset_1(sK71,sK73),X0)
    | ~ r2_hidden(sK5(k3_subset_1(sK71,sK73),X0),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_62235,plain,
    ( r1_tarski(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK73))
    | ~ r2_hidden(sK5(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK73)),k3_subset_1(sK71,sK73)) ),
    inference(instantiation,[status(thm)],[c_43727])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k3_subset_1(X1,X0))
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f1758])).

cnf(c_59402,plain,
    ( ~ m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK73,k1_zfmisc_1(sK71))
    | ~ r1_tarski(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK73))
    | r1_tarski(sK73,k3_subset_1(sK71,k3_subset_1(sK71,sK73))) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1153])).

cnf(c_29384,plain,
    ( ~ r1_tarski(X0,k3_subset_1(sK71,k3_subset_1(sK71,sK73)))
    | ~ r1_tarski(k3_subset_1(sK71,sK72),X0)
    | r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k3_subset_1(sK71,sK73))) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_47719,plain,
    ( r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k3_subset_1(sK71,sK73)))
    | ~ r1_tarski(k3_subset_1(sK71,sK72),sK73)
    | ~ r1_tarski(sK73,k3_subset_1(sK71,k3_subset_1(sK71,sK73))) ),
    inference(instantiation,[status(thm)],[c_29384])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1706])).

cnf(c_24633,plain,
    ( m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_705,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X2,X0)
    | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f1754])).

cnf(c_22566,plain,
    ( ~ m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(X0))
    | ~ r1_tarski(k3_subset_1(X0,sK72),k3_subset_1(X0,k3_subset_1(sK71,sK73)))
    | r1_tarski(k3_subset_1(sK71,sK73),sK72) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_24310,plain,
    ( ~ m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(sK71))
    | ~ r1_tarski(k3_subset_1(sK71,sK72),k3_subset_1(sK71,k3_subset_1(sK71,sK73)))
    | r1_tarski(k3_subset_1(sK71,sK73),sK72) ),
    inference(instantiation,[status(thm)],[c_22566])).

cnf(c_711,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK71,sK73),sK72) ),
    inference(cnf_transformation,[],[f1762])).

cnf(c_712,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK71,sK72),sK73) ),
    inference(cnf_transformation,[],[f1761])).

cnf(c_713,negated_conjecture,
    ( m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1760])).

cnf(c_714,negated_conjecture,
    ( m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1759])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62236,c_62235,c_59402,c_47719,c_24633,c_24310,c_711,c_712,c_713,c_714])).

%------------------------------------------------------------------------------

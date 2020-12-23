%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0365+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 18.84s
% Output     : CNFRefutation 18.84s
% Verified   : 
% Statistics : Number of formulae       :   47 (  75 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  153 ( 325 expanded)
%              Number of equality atoms :   19 (  55 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f505,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f807,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f505])).

fof(f1046,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f807])).

fof(f1791,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1046])).

fof(f461,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f758,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f461])).

fof(f1728,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f758])).

fof(f504,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f806,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f504])).

fof(f1045,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f806])).

fof(f1789,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1045])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f529,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f1099,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f529])).

fof(f506,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f507,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f506])).

fof(f808,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f507])).

fof(f809,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f808])).

fof(f1048,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k3_subset_1(X0,sK73) != X1
        & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,sK73))
        & r1_xboole_0(X1,sK73)
        & m1_subset_1(sK73,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1047,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK71,X2) != sK72
          & r1_xboole_0(k3_subset_1(sK71,sK72),k3_subset_1(sK71,X2))
          & r1_xboole_0(sK72,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK71)) )
      & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ) ),
    introduced(choice_axiom,[])).

fof(f1049,plain,
    ( k3_subset_1(sK71,sK73) != sK72
    & r1_xboole_0(k3_subset_1(sK71,sK72),k3_subset_1(sK71,sK73))
    & r1_xboole_0(sK72,sK73)
    & m1_subset_1(sK73,k1_zfmisc_1(sK71))
    & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK71,sK72,sK73])],[f809,f1048,f1047])).

fof(f1796,plain,(
    r1_xboole_0(k3_subset_1(sK71,sK72),k3_subset_1(sK71,sK73)) ),
    inference(cnf_transformation,[],[f1049])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f865,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f866,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f865])).

fof(f1124,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f866])).

fof(f1797,plain,(
    k3_subset_1(sK71,sK73) != sK72 ),
    inference(cnf_transformation,[],[f1049])).

fof(f1795,plain,(
    r1_xboole_0(sK72,sK73) ),
    inference(cnf_transformation,[],[f1049])).

fof(f1794,plain,(
    m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1049])).

fof(f1793,plain,(
    m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1049])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_subset_1(X1,X0))
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f1791])).

cnf(c_32662,plain,
    ( ~ m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(X0))
    | ~ r1_xboole_0(k3_subset_1(sK71,sK73),k3_subset_1(X0,sK72))
    | r1_tarski(k3_subset_1(sK71,sK73),sK72) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_59197,plain,
    ( ~ m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(sK71))
    | ~ r1_xboole_0(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK72))
    | r1_tarski(k3_subset_1(sK71,sK73),sK72) ),
    inference(instantiation,[status(thm)],[c_32662])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1728])).

cnf(c_41234,plain,
    ( m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X0)
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f1789])).

cnf(c_32627,plain,
    ( ~ m1_subset_1(sK72,k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK73,k1_zfmisc_1(sK71))
    | ~ r1_xboole_0(sK72,sK73)
    | r1_tarski(sK72,k3_subset_1(sK71,sK73)) ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1099])).

cnf(c_724,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(sK71,sK72),k3_subset_1(sK71,sK73)) ),
    inference(cnf_transformation,[],[f1796])).

cnf(c_27653,plain,
    ( r1_xboole_0(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK72)) ),
    inference(resolution,[status(thm)],[c_44,c_724])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1124])).

cnf(c_27580,plain,
    ( ~ r1_tarski(k3_subset_1(sK71,sK73),sK72)
    | ~ r1_tarski(sK72,k3_subset_1(sK71,sK73))
    | k3_subset_1(sK71,sK73) = sK72 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_723,negated_conjecture,
    ( k3_subset_1(sK71,sK73) != sK72 ),
    inference(cnf_transformation,[],[f1797])).

cnf(c_725,negated_conjecture,
    ( r1_xboole_0(sK72,sK73) ),
    inference(cnf_transformation,[],[f1795])).

cnf(c_726,negated_conjecture,
    ( m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1794])).

cnf(c_727,negated_conjecture,
    ( m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1793])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59197,c_41234,c_32627,c_27653,c_27580,c_723,c_725,c_726,c_727])).

%------------------------------------------------------------------------------

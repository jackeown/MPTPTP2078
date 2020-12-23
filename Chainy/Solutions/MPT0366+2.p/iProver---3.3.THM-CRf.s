%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0366+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 14.73s
% Output     : CNFRefutation 14.73s
% Verified   : 
% Statistics : Number of formulae       :   37 (  69 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  128 ( 368 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f530,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f1103,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f530])).

fof(f504,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f807,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f504])).

fof(f1048,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f807])).

fof(f1793,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1048])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f565,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f566,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f565])).

fof(f1179,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f566])).

fof(f507,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f508,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f507])).

fof(f811,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f508])).

fof(f812,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f811])).

fof(f1052,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
          & r1_xboole_0(X3,X2)
          & r1_tarski(X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(X1,k3_subset_1(X0,sK74))
        & r1_xboole_0(sK74,X2)
        & r1_tarski(X1,X2)
        & m1_subset_1(sK74,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1051,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ? [X3] :
            ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
            & r1_xboole_0(X3,sK73)
            & r1_tarski(X1,sK73)
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK73,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1050,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
                & r1_xboole_0(X3,X2)
                & r1_tarski(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(sK72,k3_subset_1(sK71,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(sK72,X2)
              & m1_subset_1(X3,k1_zfmisc_1(sK71)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK71)) )
      & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ) ),
    introduced(choice_axiom,[])).

fof(f1053,plain,
    ( ~ r1_tarski(sK72,k3_subset_1(sK71,sK74))
    & r1_xboole_0(sK74,sK73)
    & r1_tarski(sK72,sK73)
    & m1_subset_1(sK74,k1_zfmisc_1(sK71))
    & m1_subset_1(sK73,k1_zfmisc_1(sK71))
    & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK71,sK72,sK73,sK74])],[f812,f1052,f1051,f1050])).

fof(f1803,plain,(
    ~ r1_tarski(sK72,k3_subset_1(sK71,sK74)) ),
    inference(cnf_transformation,[],[f1053])).

fof(f1802,plain,(
    r1_xboole_0(sK74,sK73) ),
    inference(cnf_transformation,[],[f1053])).

fof(f1801,plain,(
    r1_tarski(sK72,sK73) ),
    inference(cnf_transformation,[],[f1053])).

fof(f1800,plain,(
    m1_subset_1(sK74,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1053])).

fof(f1799,plain,(
    m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1053])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1103])).

cnf(c_33814,plain,
    ( r1_xboole_0(sK73,sK74)
    | ~ r1_xboole_0(sK74,sK73) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X0)
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f1793])).

cnf(c_25476,plain,
    ( ~ m1_subset_1(sK73,k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK74,k1_zfmisc_1(sK71))
    | ~ r1_xboole_0(sK73,sK74)
    | r1_tarski(sK73,k3_subset_1(sK71,sK74)) ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1179])).

cnf(c_23118,plain,
    ( ~ r1_tarski(X0,k3_subset_1(sK71,sK74))
    | ~ r1_tarski(sK72,X0)
    | r1_tarski(sK72,k3_subset_1(sK71,sK74)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_24642,plain,
    ( ~ r1_tarski(sK73,k3_subset_1(sK71,sK74))
    | r1_tarski(sK72,k3_subset_1(sK71,sK74))
    | ~ r1_tarski(sK72,sK73) ),
    inference(instantiation,[status(thm)],[c_23118])).

cnf(c_724,negated_conjecture,
    ( ~ r1_tarski(sK72,k3_subset_1(sK71,sK74)) ),
    inference(cnf_transformation,[],[f1803])).

cnf(c_725,negated_conjecture,
    ( r1_xboole_0(sK74,sK73) ),
    inference(cnf_transformation,[],[f1802])).

cnf(c_726,negated_conjecture,
    ( r1_tarski(sK72,sK73) ),
    inference(cnf_transformation,[],[f1801])).

cnf(c_727,negated_conjecture,
    ( m1_subset_1(sK74,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1800])).

cnf(c_728,negated_conjecture,
    ( m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1799])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33814,c_25476,c_24642,c_724,c_725,c_726,c_727,c_728])).

%------------------------------------------------------------------------------

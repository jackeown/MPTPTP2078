%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0364+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 23.20s
% Output     : CNFRefutation 23.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  83 expanded)
%              Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  193 ( 377 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f497,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f795,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f497])).

fof(f796,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f795])).

fof(f1778,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f796])).

fof(f504,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f805,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f504])).

fof(f1042,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f805])).

fof(f1787,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1042])).

fof(f493,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f791,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f493])).

fof(f1039,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f791])).

fof(f1773,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1039])).

fof(f461,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f757,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f461])).

fof(f1726,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f757])).

fof(f1788,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1042])).

fof(f1774,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1039])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f528,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f1097,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f528])).

fof(f505,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f506,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f505])).

fof(f806,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f506])).

fof(f1043,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f806])).

fof(f1044,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f1043])).

fof(f1046,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(X1,sK73)
          | ~ r1_xboole_0(X1,k3_subset_1(X0,sK73)) )
        & ( r1_tarski(X1,sK73)
          | r1_xboole_0(X1,k3_subset_1(X0,sK73)) )
        & m1_subset_1(sK73,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1045,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK72,X2)
            | ~ r1_xboole_0(sK72,k3_subset_1(sK71,X2)) )
          & ( r1_tarski(sK72,X2)
            | r1_xboole_0(sK72,k3_subset_1(sK71,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK71)) )
      & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ) ),
    introduced(choice_axiom,[])).

fof(f1047,plain,
    ( ( ~ r1_tarski(sK72,sK73)
      | ~ r1_xboole_0(sK72,k3_subset_1(sK71,sK73)) )
    & ( r1_tarski(sK72,sK73)
      | r1_xboole_0(sK72,k3_subset_1(sK71,sK73)) )
    & m1_subset_1(sK73,k1_zfmisc_1(sK71))
    & m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK71,sK72,sK73])],[f1044,f1046,f1045])).

fof(f1792,plain,
    ( ~ r1_tarski(sK72,sK73)
    | ~ r1_xboole_0(sK72,k3_subset_1(sK71,sK73)) ),
    inference(cnf_transformation,[],[f1047])).

fof(f1791,plain,
    ( r1_tarski(sK72,sK73)
    | r1_xboole_0(sK72,k3_subset_1(sK71,sK73)) ),
    inference(cnf_transformation,[],[f1047])).

fof(f1790,plain,(
    m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1047])).

fof(f1789,plain,(
    m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1047])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k3_subset_1(X1,X0))
    | r1_tarski(X0,k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f1778])).

cnf(c_67428,plain,
    ( ~ m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(sK71))
    | ~ r1_tarski(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK72))
    | r1_tarski(sK72,k3_subset_1(sK71,k3_subset_1(sK71,sK73))) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X0)
    | r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f1787])).

cnf(c_43272,plain,
    ( ~ m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(sK71))
    | ~ r1_xboole_0(k3_subset_1(sK71,sK73),sK72)
    | r1_tarski(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK72)) ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f1773])).

cnf(c_43269,plain,
    ( ~ m1_subset_1(sK73,k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(sK71))
    | r1_tarski(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK72))
    | ~ r1_tarski(sK72,sK73) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1726])).

cnf(c_32663,plain,
    ( m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_xboole_0(X2,X0)
    | ~ r1_tarski(X2,k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f1788])).

cnf(c_22985,plain,
    ( ~ m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(X0))
    | r1_xboole_0(sK72,k3_subset_1(sK71,sK73))
    | ~ r1_tarski(sK72,k3_subset_1(X0,k3_subset_1(sK71,sK73))) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_28118,plain,
    ( ~ m1_subset_1(k3_subset_1(sK71,sK73),k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(sK71))
    | r1_xboole_0(sK72,k3_subset_1(sK71,sK73))
    | ~ r1_tarski(sK72,k3_subset_1(sK71,k3_subset_1(sK71,sK73))) ),
    inference(instantiation,[status(thm)],[c_22985])).

cnf(c_705,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X2,X0)
    | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f1774])).

cnf(c_23080,plain,
    ( ~ m1_subset_1(sK73,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(X0))
    | ~ r1_tarski(k3_subset_1(X0,sK73),k3_subset_1(X0,sK72))
    | r1_tarski(sK72,sK73) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_26518,plain,
    ( ~ m1_subset_1(sK73,k1_zfmisc_1(sK71))
    | ~ m1_subset_1(sK72,k1_zfmisc_1(sK71))
    | ~ r1_tarski(k3_subset_1(sK71,sK73),k3_subset_1(sK71,sK72))
    | r1_tarski(sK72,sK73) ),
    inference(instantiation,[status(thm)],[c_23080])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1097])).

cnf(c_24478,plain,
    ( r1_xboole_0(k3_subset_1(sK71,sK73),sK72)
    | ~ r1_xboole_0(sK72,k3_subset_1(sK71,sK73)) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_721,negated_conjecture,
    ( ~ r1_xboole_0(sK72,k3_subset_1(sK71,sK73))
    | ~ r1_tarski(sK72,sK73) ),
    inference(cnf_transformation,[],[f1792])).

cnf(c_722,negated_conjecture,
    ( r1_xboole_0(sK72,k3_subset_1(sK71,sK73))
    | r1_tarski(sK72,sK73) ),
    inference(cnf_transformation,[],[f1791])).

cnf(c_723,negated_conjecture,
    ( m1_subset_1(sK73,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1790])).

cnf(c_724,negated_conjecture,
    ( m1_subset_1(sK72,k1_zfmisc_1(sK71)) ),
    inference(cnf_transformation,[],[f1789])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_67428,c_43272,c_43269,c_32663,c_28118,c_26518,c_24478,c_721,c_722,c_723,c_724])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:04 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 324 expanded)
%              Number of clauses        :   55 (  60 expanded)
%              Number of leaves         :   26 (  86 expanded)
%              Depth                    :   19
%              Number of atoms          :  471 ( 895 expanded)
%              Number of equality atoms :  191 ( 385 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f55])).

fof(f59,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) = X2
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1)
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f56,f59,f58,f57])).

fof(f98,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f141,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f142,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f141])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK11,sK10) != sK9
      & r2_hidden(sK10,sK8)
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_tarski(sK9))))
      & v1_funct_2(sK11,sK8,k1_tarski(sK9))
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( k1_funct_1(sK11,sK10) != sK9
    & r2_hidden(sK10,sK8)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_tarski(sK9))))
    & v1_funct_2(sK11,sK8,k1_tarski(sK9))
    & v1_funct_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f34,f62])).

fof(f112,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f63])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f113,plain,(
    v1_funct_2(sK11,sK8,k1_tarski(sK9)) ),
    inference(cnf_transformation,[],[f63])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f76,f117])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f75,f118])).

fof(f120,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f119])).

fof(f121,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f120])).

fof(f122,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f121])).

fof(f128,plain,(
    v1_funct_2(sK11,sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)) ),
    inference(definition_unfolding,[],[f113,f122])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f114,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_tarski(sK9)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f127,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)))) ),
    inference(definition_unfolding,[],[f114,f122])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f3])).

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

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f122])).

fof(f129,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f125])).

fof(f130,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f129])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f122])).

fof(f131,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f126])).

fof(f116,plain,(
    k1_funct_1(sK11,sK10) != sK9 ),
    inference(cnf_transformation,[],[f63])).

fof(f115,plain,(
    r2_hidden(sK10,sK8) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2693,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5616,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK10,sK8)
    | X1 != sK8
    | X0 != sK10 ),
    inference(instantiation,[status(thm)],[c_2693])).

cnf(c_16930,plain,
    ( r2_hidden(X0,k1_relat_1(sK11))
    | ~ r2_hidden(sK10,sK8)
    | X0 != sK10
    | k1_relat_1(sK11) != sK8 ),
    inference(instantiation,[status(thm)],[c_5616])).

cnf(c_23798,plain,
    ( r2_hidden(sK10,k1_relat_1(sK11))
    | ~ r2_hidden(sK10,sK8)
    | k1_relat_1(sK11) != sK8
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_16930])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_961,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_45])).

cnf(c_962,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK11))
    | r2_hidden(k1_funct_1(sK11,X0),k2_relat_1(sK11))
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_13627,plain,
    ( r2_hidden(k1_funct_1(sK11,sK10),k2_relat_1(sK11))
    | ~ r2_hidden(sK10,k1_relat_1(sK11))
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3265,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK11,sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_635,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK11 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_43])).

cnf(c_636,plain,
    ( ~ v1_funct_2(sK11,X0,X1)
    | k1_relset_1(X0,X1,sK11) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_1291,plain,
    ( k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9) != X0
    | k1_relset_1(X1,X0,sK11) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | sK8 != X1
    | sK11 != sK11
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_636])).

cnf(c_1292,plain,
    ( k1_relset_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9),sK11) = sK8
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)))
    | k1_xboole_0 = k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9) ),
    inference(unflattening,[status(thm)],[c_1291])).

cnf(c_1771,plain,
    ( k1_relset_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9),sK11) = sK8
    | k1_xboole_0 = k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9) ),
    inference(equality_resolution_simp,[status(thm)],[c_1292])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_671,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_43])).

cnf(c_672,plain,
    ( k1_relset_1(X0,X1,sK11) = k1_relat_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_3483,plain,
    ( k1_relset_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9),sK11) = k1_relat_1(sK11) ),
    inference(equality_resolution,[status(thm)],[c_672])).

cnf(c_3858,plain,
    ( k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9) = k1_xboole_0
    | k1_relat_1(sK11) = sK8 ),
    inference(demodulation,[status(thm)],[c_1771,c_3483])).

cnf(c_6,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_3262,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5987,plain,
    ( k1_relat_1(sK11) = sK8
    | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3858,c_3262])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3245,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11022,plain,
    ( k1_relat_1(sK11) = sK8
    | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5987,c_3245])).

cnf(c_11378,plain,
    ( k1_relat_1(sK11) = sK8 ),
    inference(superposition,[status(thm)],[c_3265,c_11022])).

cnf(c_2690,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6626,plain,
    ( sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_2690])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3377,plain,
    ( ~ r2_hidden(k1_funct_1(sK11,sK10),X0)
    | r2_hidden(k1_funct_1(sK11,sK10),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))
    | ~ r1_tarski(X0,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5418,plain,
    ( r2_hidden(k1_funct_1(sK11,sK10),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))
    | ~ r2_hidden(k1_funct_1(sK11,sK10),k2_relat_1(sK11))
    | ~ r1_tarski(k2_relat_1(sK11),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)) ),
    inference(instantiation,[status(thm)],[c_3377])).

cnf(c_3500,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) = k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) ),
    inference(instantiation,[status(thm)],[c_2690])).

cnf(c_24,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_495,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_32])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_623,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_496,c_43])).

cnf(c_624,plain,
    ( r1_tarski(k2_relat_1(sK11),X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_3421,plain,
    ( r1_tarski(k2_relat_1(sK11),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_680,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_43])).

cnf(c_681,plain,
    ( v1_relat_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_3359,plain,
    ( v1_relat_1(sK11)
    | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_3313,plain,
    ( ~ r2_hidden(k1_funct_1(sK11,sK10),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))
    | k1_funct_1(sK11,sK10) = sK9 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_41,negated_conjecture,
    ( k1_funct_1(sK11,sK10) != sK9 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_42,negated_conjecture,
    ( r2_hidden(sK10,sK8) ),
    inference(cnf_transformation,[],[f115])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23798,c_13627,c_11378,c_6626,c_5418,c_3500,c_3421,c_3359,c_3313,c_41,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:00:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.79/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.79/1.48  
% 7.79/1.48  ------  iProver source info
% 7.79/1.48  
% 7.79/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.79/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.79/1.48  git: non_committed_changes: false
% 7.79/1.48  git: last_make_outside_of_git: false
% 7.79/1.48  
% 7.79/1.48  ------ 
% 7.79/1.48  
% 7.79/1.48  ------ Input Options
% 7.79/1.48  
% 7.79/1.48  --out_options                           all
% 7.79/1.48  --tptp_safe_out                         true
% 7.79/1.48  --problem_path                          ""
% 7.79/1.48  --include_path                          ""
% 7.79/1.48  --clausifier                            res/vclausify_rel
% 7.79/1.48  --clausifier_options                    ""
% 7.79/1.48  --stdin                                 false
% 7.79/1.48  --stats_out                             all
% 7.79/1.48  
% 7.79/1.48  ------ General Options
% 7.79/1.48  
% 7.79/1.48  --fof                                   false
% 7.79/1.48  --time_out_real                         305.
% 7.79/1.48  --time_out_virtual                      -1.
% 7.79/1.48  --symbol_type_check                     false
% 7.79/1.48  --clausify_out                          false
% 7.79/1.48  --sig_cnt_out                           false
% 7.79/1.48  --trig_cnt_out                          false
% 7.79/1.48  --trig_cnt_out_tolerance                1.
% 7.79/1.48  --trig_cnt_out_sk_spl                   false
% 7.79/1.48  --abstr_cl_out                          false
% 7.79/1.48  
% 7.79/1.48  ------ Global Options
% 7.79/1.48  
% 7.79/1.48  --schedule                              default
% 7.79/1.48  --add_important_lit                     false
% 7.79/1.48  --prop_solver_per_cl                    1000
% 7.79/1.48  --min_unsat_core                        false
% 7.79/1.48  --soft_assumptions                      false
% 7.79/1.48  --soft_lemma_size                       3
% 7.79/1.48  --prop_impl_unit_size                   0
% 7.79/1.48  --prop_impl_unit                        []
% 7.79/1.48  --share_sel_clauses                     true
% 7.79/1.48  --reset_solvers                         false
% 7.79/1.48  --bc_imp_inh                            [conj_cone]
% 7.79/1.48  --conj_cone_tolerance                   3.
% 7.79/1.48  --extra_neg_conj                        none
% 7.79/1.48  --large_theory_mode                     true
% 7.79/1.48  --prolific_symb_bound                   200
% 7.79/1.48  --lt_threshold                          2000
% 7.79/1.48  --clause_weak_htbl                      true
% 7.79/1.48  --gc_record_bc_elim                     false
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing Options
% 7.79/1.48  
% 7.79/1.48  --preprocessing_flag                    true
% 7.79/1.48  --time_out_prep_mult                    0.1
% 7.79/1.48  --splitting_mode                        input
% 7.79/1.48  --splitting_grd                         true
% 7.79/1.48  --splitting_cvd                         false
% 7.79/1.48  --splitting_cvd_svl                     false
% 7.79/1.48  --splitting_nvd                         32
% 7.79/1.48  --sub_typing                            true
% 7.79/1.48  --prep_gs_sim                           true
% 7.79/1.48  --prep_unflatten                        true
% 7.79/1.48  --prep_res_sim                          true
% 7.79/1.48  --prep_upred                            true
% 7.79/1.48  --prep_sem_filter                       exhaustive
% 7.79/1.48  --prep_sem_filter_out                   false
% 7.79/1.48  --pred_elim                             true
% 7.79/1.48  --res_sim_input                         true
% 7.79/1.48  --eq_ax_congr_red                       true
% 7.79/1.48  --pure_diseq_elim                       true
% 7.79/1.48  --brand_transform                       false
% 7.79/1.48  --non_eq_to_eq                          false
% 7.79/1.48  --prep_def_merge                        true
% 7.79/1.48  --prep_def_merge_prop_impl              false
% 7.79/1.48  --prep_def_merge_mbd                    true
% 7.79/1.48  --prep_def_merge_tr_red                 false
% 7.79/1.48  --prep_def_merge_tr_cl                  false
% 7.79/1.48  --smt_preprocessing                     true
% 7.79/1.48  --smt_ac_axioms                         fast
% 7.79/1.48  --preprocessed_out                      false
% 7.79/1.48  --preprocessed_stats                    false
% 7.79/1.48  
% 7.79/1.48  ------ Abstraction refinement Options
% 7.79/1.48  
% 7.79/1.48  --abstr_ref                             []
% 7.79/1.48  --abstr_ref_prep                        false
% 7.79/1.48  --abstr_ref_until_sat                   false
% 7.79/1.48  --abstr_ref_sig_restrict                funpre
% 7.79/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.48  --abstr_ref_under                       []
% 7.79/1.48  
% 7.79/1.48  ------ SAT Options
% 7.79/1.48  
% 7.79/1.48  --sat_mode                              false
% 7.79/1.48  --sat_fm_restart_options                ""
% 7.79/1.48  --sat_gr_def                            false
% 7.79/1.48  --sat_epr_types                         true
% 7.79/1.48  --sat_non_cyclic_types                  false
% 7.79/1.48  --sat_finite_models                     false
% 7.79/1.48  --sat_fm_lemmas                         false
% 7.79/1.48  --sat_fm_prep                           false
% 7.79/1.48  --sat_fm_uc_incr                        true
% 7.79/1.48  --sat_out_model                         small
% 7.79/1.48  --sat_out_clauses                       false
% 7.79/1.48  
% 7.79/1.48  ------ QBF Options
% 7.79/1.48  
% 7.79/1.48  --qbf_mode                              false
% 7.79/1.48  --qbf_elim_univ                         false
% 7.79/1.48  --qbf_dom_inst                          none
% 7.79/1.48  --qbf_dom_pre_inst                      false
% 7.79/1.48  --qbf_sk_in                             false
% 7.79/1.48  --qbf_pred_elim                         true
% 7.79/1.48  --qbf_split                             512
% 7.79/1.48  
% 7.79/1.48  ------ BMC1 Options
% 7.79/1.48  
% 7.79/1.48  --bmc1_incremental                      false
% 7.79/1.48  --bmc1_axioms                           reachable_all
% 7.79/1.48  --bmc1_min_bound                        0
% 7.79/1.48  --bmc1_max_bound                        -1
% 7.79/1.48  --bmc1_max_bound_default                -1
% 7.79/1.48  --bmc1_symbol_reachability              true
% 7.79/1.48  --bmc1_property_lemmas                  false
% 7.79/1.48  --bmc1_k_induction                      false
% 7.79/1.48  --bmc1_non_equiv_states                 false
% 7.79/1.48  --bmc1_deadlock                         false
% 7.79/1.48  --bmc1_ucm                              false
% 7.79/1.48  --bmc1_add_unsat_core                   none
% 7.79/1.48  --bmc1_unsat_core_children              false
% 7.79/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.48  --bmc1_out_stat                         full
% 7.79/1.48  --bmc1_ground_init                      false
% 7.79/1.48  --bmc1_pre_inst_next_state              false
% 7.79/1.48  --bmc1_pre_inst_state                   false
% 7.79/1.48  --bmc1_pre_inst_reach_state             false
% 7.79/1.48  --bmc1_out_unsat_core                   false
% 7.79/1.48  --bmc1_aig_witness_out                  false
% 7.79/1.48  --bmc1_verbose                          false
% 7.79/1.48  --bmc1_dump_clauses_tptp                false
% 7.79/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.48  --bmc1_dump_file                        -
% 7.79/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.48  --bmc1_ucm_extend_mode                  1
% 7.79/1.48  --bmc1_ucm_init_mode                    2
% 7.79/1.48  --bmc1_ucm_cone_mode                    none
% 7.79/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.48  --bmc1_ucm_relax_model                  4
% 7.79/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.48  --bmc1_ucm_layered_model                none
% 7.79/1.48  --bmc1_ucm_max_lemma_size               10
% 7.79/1.48  
% 7.79/1.48  ------ AIG Options
% 7.79/1.48  
% 7.79/1.48  --aig_mode                              false
% 7.79/1.48  
% 7.79/1.48  ------ Instantiation Options
% 7.79/1.48  
% 7.79/1.48  --instantiation_flag                    true
% 7.79/1.48  --inst_sos_flag                         true
% 7.79/1.48  --inst_sos_phase                        true
% 7.79/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel_side                     num_symb
% 7.79/1.48  --inst_solver_per_active                1400
% 7.79/1.48  --inst_solver_calls_frac                1.
% 7.79/1.48  --inst_passive_queue_type               priority_queues
% 7.79/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.48  --inst_passive_queues_freq              [25;2]
% 7.79/1.48  --inst_dismatching                      true
% 7.79/1.48  --inst_eager_unprocessed_to_passive     true
% 7.79/1.48  --inst_prop_sim_given                   true
% 7.79/1.48  --inst_prop_sim_new                     false
% 7.79/1.48  --inst_subs_new                         false
% 7.79/1.48  --inst_eq_res_simp                      false
% 7.79/1.48  --inst_subs_given                       false
% 7.79/1.48  --inst_orphan_elimination               true
% 7.79/1.48  --inst_learning_loop_flag               true
% 7.79/1.48  --inst_learning_start                   3000
% 7.79/1.48  --inst_learning_factor                  2
% 7.79/1.48  --inst_start_prop_sim_after_learn       3
% 7.79/1.48  --inst_sel_renew                        solver
% 7.79/1.48  --inst_lit_activity_flag                true
% 7.79/1.48  --inst_restr_to_given                   false
% 7.79/1.48  --inst_activity_threshold               500
% 7.79/1.48  --inst_out_proof                        true
% 7.79/1.48  
% 7.79/1.48  ------ Resolution Options
% 7.79/1.48  
% 7.79/1.48  --resolution_flag                       true
% 7.79/1.48  --res_lit_sel                           adaptive
% 7.79/1.48  --res_lit_sel_side                      none
% 7.79/1.48  --res_ordering                          kbo
% 7.79/1.48  --res_to_prop_solver                    active
% 7.79/1.48  --res_prop_simpl_new                    false
% 7.79/1.48  --res_prop_simpl_given                  true
% 7.79/1.48  --res_passive_queue_type                priority_queues
% 7.79/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.48  --res_passive_queues_freq               [15;5]
% 7.79/1.48  --res_forward_subs                      full
% 7.79/1.48  --res_backward_subs                     full
% 7.79/1.48  --res_forward_subs_resolution           true
% 7.79/1.48  --res_backward_subs_resolution          true
% 7.79/1.48  --res_orphan_elimination                true
% 7.79/1.48  --res_time_limit                        2.
% 7.79/1.48  --res_out_proof                         true
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Options
% 7.79/1.48  
% 7.79/1.48  --superposition_flag                    true
% 7.79/1.48  --sup_passive_queue_type                priority_queues
% 7.79/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.79/1.48  --demod_completeness_check              fast
% 7.79/1.48  --demod_use_ground                      true
% 7.79/1.48  --sup_to_prop_solver                    passive
% 7.79/1.48  --sup_prop_simpl_new                    true
% 7.79/1.48  --sup_prop_simpl_given                  true
% 7.79/1.48  --sup_fun_splitting                     true
% 7.79/1.48  --sup_smt_interval                      50000
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Simplification Setup
% 7.79/1.48  
% 7.79/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.79/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.79/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.79/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.79/1.48  --sup_immed_triv                        [TrivRules]
% 7.79/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_bw_main                     []
% 7.79/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.79/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_input_bw                          []
% 7.79/1.48  
% 7.79/1.48  ------ Combination Options
% 7.79/1.48  
% 7.79/1.48  --comb_res_mult                         3
% 7.79/1.48  --comb_sup_mult                         2
% 7.79/1.48  --comb_inst_mult                        10
% 7.79/1.48  
% 7.79/1.48  ------ Debug Options
% 7.79/1.48  
% 7.79/1.48  --dbg_backtrace                         false
% 7.79/1.48  --dbg_dump_prop_clauses                 false
% 7.79/1.48  --dbg_dump_prop_clauses_file            -
% 7.79/1.48  --dbg_out_stat                          false
% 7.79/1.48  ------ Parsing...
% 7.79/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.79/1.48  ------ Proving...
% 7.79/1.48  ------ Problem Properties 
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  clauses                                 38
% 7.79/1.48  conjectures                             2
% 7.79/1.48  EPR                                     15
% 7.79/1.48  Horn                                    30
% 7.79/1.48  unary                                   13
% 7.79/1.48  binary                                  9
% 7.79/1.48  lits                                    90
% 7.79/1.48  lits eq                                 34
% 7.79/1.48  fd_pure                                 0
% 7.79/1.48  fd_pseudo                               0
% 7.79/1.48  fd_cond                                 3
% 7.79/1.48  fd_pseudo_cond                          4
% 7.79/1.48  AC symbols                              0
% 7.79/1.48  
% 7.79/1.48  ------ Schedule dynamic 5 is on 
% 7.79/1.48  
% 7.79/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  ------ 
% 7.79/1.48  Current options:
% 7.79/1.48  ------ 
% 7.79/1.48  
% 7.79/1.48  ------ Input Options
% 7.79/1.48  
% 7.79/1.48  --out_options                           all
% 7.79/1.48  --tptp_safe_out                         true
% 7.79/1.48  --problem_path                          ""
% 7.79/1.48  --include_path                          ""
% 7.79/1.48  --clausifier                            res/vclausify_rel
% 7.79/1.48  --clausifier_options                    ""
% 7.79/1.48  --stdin                                 false
% 7.79/1.48  --stats_out                             all
% 7.79/1.48  
% 7.79/1.48  ------ General Options
% 7.79/1.48  
% 7.79/1.48  --fof                                   false
% 7.79/1.48  --time_out_real                         305.
% 7.79/1.48  --time_out_virtual                      -1.
% 7.79/1.48  --symbol_type_check                     false
% 7.79/1.48  --clausify_out                          false
% 7.79/1.48  --sig_cnt_out                           false
% 7.79/1.48  --trig_cnt_out                          false
% 7.79/1.48  --trig_cnt_out_tolerance                1.
% 7.79/1.48  --trig_cnt_out_sk_spl                   false
% 7.79/1.48  --abstr_cl_out                          false
% 7.79/1.48  
% 7.79/1.48  ------ Global Options
% 7.79/1.48  
% 7.79/1.48  --schedule                              default
% 7.79/1.48  --add_important_lit                     false
% 7.79/1.48  --prop_solver_per_cl                    1000
% 7.79/1.48  --min_unsat_core                        false
% 7.79/1.48  --soft_assumptions                      false
% 7.79/1.48  --soft_lemma_size                       3
% 7.79/1.48  --prop_impl_unit_size                   0
% 7.79/1.48  --prop_impl_unit                        []
% 7.79/1.48  --share_sel_clauses                     true
% 7.79/1.48  --reset_solvers                         false
% 7.79/1.48  --bc_imp_inh                            [conj_cone]
% 7.79/1.48  --conj_cone_tolerance                   3.
% 7.79/1.48  --extra_neg_conj                        none
% 7.79/1.48  --large_theory_mode                     true
% 7.79/1.48  --prolific_symb_bound                   200
% 7.79/1.48  --lt_threshold                          2000
% 7.79/1.48  --clause_weak_htbl                      true
% 7.79/1.48  --gc_record_bc_elim                     false
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing Options
% 7.79/1.48  
% 7.79/1.48  --preprocessing_flag                    true
% 7.79/1.48  --time_out_prep_mult                    0.1
% 7.79/1.48  --splitting_mode                        input
% 7.79/1.48  --splitting_grd                         true
% 7.79/1.48  --splitting_cvd                         false
% 7.79/1.48  --splitting_cvd_svl                     false
% 7.79/1.48  --splitting_nvd                         32
% 7.79/1.48  --sub_typing                            true
% 7.79/1.48  --prep_gs_sim                           true
% 7.79/1.48  --prep_unflatten                        true
% 7.79/1.48  --prep_res_sim                          true
% 7.79/1.48  --prep_upred                            true
% 7.79/1.48  --prep_sem_filter                       exhaustive
% 7.79/1.48  --prep_sem_filter_out                   false
% 7.79/1.48  --pred_elim                             true
% 7.79/1.48  --res_sim_input                         true
% 7.79/1.48  --eq_ax_congr_red                       true
% 7.79/1.48  --pure_diseq_elim                       true
% 7.79/1.48  --brand_transform                       false
% 7.79/1.48  --non_eq_to_eq                          false
% 7.79/1.48  --prep_def_merge                        true
% 7.79/1.48  --prep_def_merge_prop_impl              false
% 7.79/1.48  --prep_def_merge_mbd                    true
% 7.79/1.48  --prep_def_merge_tr_red                 false
% 7.79/1.48  --prep_def_merge_tr_cl                  false
% 7.79/1.48  --smt_preprocessing                     true
% 7.79/1.48  --smt_ac_axioms                         fast
% 7.79/1.48  --preprocessed_out                      false
% 7.79/1.48  --preprocessed_stats                    false
% 7.79/1.48  
% 7.79/1.48  ------ Abstraction refinement Options
% 7.79/1.48  
% 7.79/1.48  --abstr_ref                             []
% 7.79/1.48  --abstr_ref_prep                        false
% 7.79/1.48  --abstr_ref_until_sat                   false
% 7.79/1.48  --abstr_ref_sig_restrict                funpre
% 7.79/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.48  --abstr_ref_under                       []
% 7.79/1.48  
% 7.79/1.48  ------ SAT Options
% 7.79/1.48  
% 7.79/1.48  --sat_mode                              false
% 7.79/1.48  --sat_fm_restart_options                ""
% 7.79/1.48  --sat_gr_def                            false
% 7.79/1.48  --sat_epr_types                         true
% 7.79/1.48  --sat_non_cyclic_types                  false
% 7.79/1.48  --sat_finite_models                     false
% 7.79/1.48  --sat_fm_lemmas                         false
% 7.79/1.48  --sat_fm_prep                           false
% 7.79/1.48  --sat_fm_uc_incr                        true
% 7.79/1.48  --sat_out_model                         small
% 7.79/1.48  --sat_out_clauses                       false
% 7.79/1.48  
% 7.79/1.48  ------ QBF Options
% 7.79/1.48  
% 7.79/1.48  --qbf_mode                              false
% 7.79/1.48  --qbf_elim_univ                         false
% 7.79/1.48  --qbf_dom_inst                          none
% 7.79/1.48  --qbf_dom_pre_inst                      false
% 7.79/1.48  --qbf_sk_in                             false
% 7.79/1.48  --qbf_pred_elim                         true
% 7.79/1.48  --qbf_split                             512
% 7.79/1.48  
% 7.79/1.48  ------ BMC1 Options
% 7.79/1.48  
% 7.79/1.48  --bmc1_incremental                      false
% 7.79/1.48  --bmc1_axioms                           reachable_all
% 7.79/1.48  --bmc1_min_bound                        0
% 7.79/1.48  --bmc1_max_bound                        -1
% 7.79/1.48  --bmc1_max_bound_default                -1
% 7.79/1.48  --bmc1_symbol_reachability              true
% 7.79/1.48  --bmc1_property_lemmas                  false
% 7.79/1.48  --bmc1_k_induction                      false
% 7.79/1.48  --bmc1_non_equiv_states                 false
% 7.79/1.48  --bmc1_deadlock                         false
% 7.79/1.48  --bmc1_ucm                              false
% 7.79/1.48  --bmc1_add_unsat_core                   none
% 7.79/1.48  --bmc1_unsat_core_children              false
% 7.79/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.48  --bmc1_out_stat                         full
% 7.79/1.48  --bmc1_ground_init                      false
% 7.79/1.48  --bmc1_pre_inst_next_state              false
% 7.79/1.48  --bmc1_pre_inst_state                   false
% 7.79/1.48  --bmc1_pre_inst_reach_state             false
% 7.79/1.48  --bmc1_out_unsat_core                   false
% 7.79/1.48  --bmc1_aig_witness_out                  false
% 7.79/1.48  --bmc1_verbose                          false
% 7.79/1.48  --bmc1_dump_clauses_tptp                false
% 7.79/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.48  --bmc1_dump_file                        -
% 7.79/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.48  --bmc1_ucm_extend_mode                  1
% 7.79/1.48  --bmc1_ucm_init_mode                    2
% 7.79/1.48  --bmc1_ucm_cone_mode                    none
% 7.79/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.48  --bmc1_ucm_relax_model                  4
% 7.79/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.48  --bmc1_ucm_layered_model                none
% 7.79/1.48  --bmc1_ucm_max_lemma_size               10
% 7.79/1.48  
% 7.79/1.48  ------ AIG Options
% 7.79/1.48  
% 7.79/1.48  --aig_mode                              false
% 7.79/1.48  
% 7.79/1.48  ------ Instantiation Options
% 7.79/1.48  
% 7.79/1.48  --instantiation_flag                    true
% 7.79/1.48  --inst_sos_flag                         true
% 7.79/1.48  --inst_sos_phase                        true
% 7.79/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel_side                     none
% 7.79/1.48  --inst_solver_per_active                1400
% 7.79/1.48  --inst_solver_calls_frac                1.
% 7.79/1.48  --inst_passive_queue_type               priority_queues
% 7.79/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.48  --inst_passive_queues_freq              [25;2]
% 7.79/1.48  --inst_dismatching                      true
% 7.79/1.48  --inst_eager_unprocessed_to_passive     true
% 7.79/1.48  --inst_prop_sim_given                   true
% 7.79/1.48  --inst_prop_sim_new                     false
% 7.79/1.48  --inst_subs_new                         false
% 7.79/1.48  --inst_eq_res_simp                      false
% 7.79/1.48  --inst_subs_given                       false
% 7.79/1.48  --inst_orphan_elimination               true
% 7.79/1.48  --inst_learning_loop_flag               true
% 7.79/1.48  --inst_learning_start                   3000
% 7.79/1.48  --inst_learning_factor                  2
% 7.79/1.48  --inst_start_prop_sim_after_learn       3
% 7.79/1.48  --inst_sel_renew                        solver
% 7.79/1.48  --inst_lit_activity_flag                true
% 7.79/1.48  --inst_restr_to_given                   false
% 7.79/1.48  --inst_activity_threshold               500
% 7.79/1.48  --inst_out_proof                        true
% 7.79/1.48  
% 7.79/1.48  ------ Resolution Options
% 7.79/1.48  
% 7.79/1.48  --resolution_flag                       false
% 7.79/1.48  --res_lit_sel                           adaptive
% 7.79/1.48  --res_lit_sel_side                      none
% 7.79/1.48  --res_ordering                          kbo
% 7.79/1.48  --res_to_prop_solver                    active
% 7.79/1.48  --res_prop_simpl_new                    false
% 7.79/1.48  --res_prop_simpl_given                  true
% 7.79/1.48  --res_passive_queue_type                priority_queues
% 7.79/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.48  --res_passive_queues_freq               [15;5]
% 7.79/1.48  --res_forward_subs                      full
% 7.79/1.48  --res_backward_subs                     full
% 7.79/1.48  --res_forward_subs_resolution           true
% 7.79/1.48  --res_backward_subs_resolution          true
% 7.79/1.48  --res_orphan_elimination                true
% 7.79/1.48  --res_time_limit                        2.
% 7.79/1.48  --res_out_proof                         true
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Options
% 7.79/1.48  
% 7.79/1.48  --superposition_flag                    true
% 7.79/1.48  --sup_passive_queue_type                priority_queues
% 7.79/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.79/1.48  --demod_completeness_check              fast
% 7.79/1.48  --demod_use_ground                      true
% 7.79/1.48  --sup_to_prop_solver                    passive
% 7.79/1.48  --sup_prop_simpl_new                    true
% 7.79/1.48  --sup_prop_simpl_given                  true
% 7.79/1.48  --sup_fun_splitting                     true
% 7.79/1.48  --sup_smt_interval                      50000
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Simplification Setup
% 7.79/1.48  
% 7.79/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.79/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.79/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.79/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.79/1.48  --sup_immed_triv                        [TrivRules]
% 7.79/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_bw_main                     []
% 7.79/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.79/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_input_bw                          []
% 7.79/1.48  
% 7.79/1.48  ------ Combination Options
% 7.79/1.48  
% 7.79/1.48  --comb_res_mult                         3
% 7.79/1.48  --comb_sup_mult                         2
% 7.79/1.48  --comb_inst_mult                        10
% 7.79/1.48  
% 7.79/1.48  ------ Debug Options
% 7.79/1.48  
% 7.79/1.48  --dbg_backtrace                         false
% 7.79/1.48  --dbg_dump_prop_clauses                 false
% 7.79/1.48  --dbg_dump_prop_clauses_file            -
% 7.79/1.48  --dbg_out_stat                          false
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  ------ Proving...
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  % SZS status Theorem for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  fof(f13,axiom,(
% 7.79/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f25,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.79/1.48    inference(ennf_transformation,[],[f13])).
% 7.79/1.48  
% 7.79/1.48  fof(f26,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(flattening,[],[f25])).
% 7.79/1.48  
% 7.79/1.48  fof(f55,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(nnf_transformation,[],[f26])).
% 7.79/1.48  
% 7.79/1.48  fof(f56,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(rectify,[],[f55])).
% 7.79/1.48  
% 7.79/1.48  fof(f59,plain,(
% 7.79/1.48    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f58,plain,(
% 7.79/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X1)) = X2 & r2_hidden(sK6(X0,X1),k1_relat_1(X0))))) )),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f57,plain,(
% 7.79/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1))))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f60,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & ((k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f56,f59,f58,f57])).
% 7.79/1.48  
% 7.79/1.48  fof(f98,plain,(
% 7.79/1.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f60])).
% 7.79/1.48  
% 7.79/1.48  fof(f141,plain,(
% 7.79/1.48    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(equality_resolution,[],[f98])).
% 7.79/1.48  
% 7.79/1.48  fof(f142,plain,(
% 7.79/1.48    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(equality_resolution,[],[f141])).
% 7.79/1.48  
% 7.79/1.48  fof(f19,conjecture,(
% 7.79/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f20,negated_conjecture,(
% 7.79/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.79/1.48    inference(negated_conjecture,[],[f19])).
% 7.79/1.48  
% 7.79/1.48  fof(f33,plain,(
% 7.79/1.48    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 7.79/1.48    inference(ennf_transformation,[],[f20])).
% 7.79/1.48  
% 7.79/1.48  fof(f34,plain,(
% 7.79/1.48    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 7.79/1.48    inference(flattening,[],[f33])).
% 7.79/1.48  
% 7.79/1.48  fof(f62,plain,(
% 7.79/1.48    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK11,sK10) != sK9 & r2_hidden(sK10,sK8) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_tarski(sK9)))) & v1_funct_2(sK11,sK8,k1_tarski(sK9)) & v1_funct_1(sK11))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f63,plain,(
% 7.79/1.48    k1_funct_1(sK11,sK10) != sK9 & r2_hidden(sK10,sK8) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_tarski(sK9)))) & v1_funct_2(sK11,sK8,k1_tarski(sK9)) & v1_funct_1(sK11)),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f34,f62])).
% 7.79/1.48  
% 7.79/1.48  fof(f112,plain,(
% 7.79/1.48    v1_funct_1(sK11)),
% 7.79/1.48    inference(cnf_transformation,[],[f63])).
% 7.79/1.48  
% 7.79/1.48  fof(f2,axiom,(
% 7.79/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f67,plain,(
% 7.79/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f2])).
% 7.79/1.48  
% 7.79/1.48  fof(f113,plain,(
% 7.79/1.48    v1_funct_2(sK11,sK8,k1_tarski(sK9))),
% 7.79/1.48    inference(cnf_transformation,[],[f63])).
% 7.79/1.48  
% 7.79/1.48  fof(f4,axiom,(
% 7.79/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f72,plain,(
% 7.79/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f4])).
% 7.79/1.48  
% 7.79/1.48  fof(f5,axiom,(
% 7.79/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f73,plain,(
% 7.79/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f5])).
% 7.79/1.48  
% 7.79/1.48  fof(f6,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f74,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f6])).
% 7.79/1.48  
% 7.79/1.48  fof(f7,axiom,(
% 7.79/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f75,plain,(
% 7.79/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f7])).
% 7.79/1.48  
% 7.79/1.48  fof(f8,axiom,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f76,plain,(
% 7.79/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f8])).
% 7.79/1.48  
% 7.79/1.48  fof(f9,axiom,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f77,plain,(
% 7.79/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f9])).
% 7.79/1.48  
% 7.79/1.48  fof(f10,axiom,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f78,plain,(
% 7.79/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f10])).
% 7.79/1.48  
% 7.79/1.48  fof(f117,plain,(
% 7.79/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.79/1.48    inference(definition_unfolding,[],[f77,f78])).
% 7.79/1.48  
% 7.79/1.48  fof(f118,plain,(
% 7.79/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.79/1.48    inference(definition_unfolding,[],[f76,f117])).
% 7.79/1.48  
% 7.79/1.48  fof(f119,plain,(
% 7.79/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.79/1.48    inference(definition_unfolding,[],[f75,f118])).
% 7.79/1.48  
% 7.79/1.48  fof(f120,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.79/1.48    inference(definition_unfolding,[],[f74,f119])).
% 7.79/1.48  
% 7.79/1.48  fof(f121,plain,(
% 7.79/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.79/1.48    inference(definition_unfolding,[],[f73,f120])).
% 7.79/1.48  
% 7.79/1.48  fof(f122,plain,(
% 7.79/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.79/1.48    inference(definition_unfolding,[],[f72,f121])).
% 7.79/1.48  
% 7.79/1.48  fof(f128,plain,(
% 7.79/1.48    v1_funct_2(sK11,sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))),
% 7.79/1.48    inference(definition_unfolding,[],[f113,f122])).
% 7.79/1.48  
% 7.79/1.48  fof(f18,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f31,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f18])).
% 7.79/1.48  
% 7.79/1.48  fof(f32,plain,(
% 7.79/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(flattening,[],[f31])).
% 7.79/1.48  
% 7.79/1.48  fof(f61,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(nnf_transformation,[],[f32])).
% 7.79/1.48  
% 7.79/1.48  fof(f106,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f61])).
% 7.79/1.48  
% 7.79/1.48  fof(f114,plain,(
% 7.79/1.48    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k1_tarski(sK9))))),
% 7.79/1.48    inference(cnf_transformation,[],[f63])).
% 7.79/1.48  
% 7.79/1.48  fof(f127,plain,(
% 7.79/1.48    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))))),
% 7.79/1.48    inference(definition_unfolding,[],[f114,f122])).
% 7.79/1.48  
% 7.79/1.48  fof(f17,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f30,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f17])).
% 7.79/1.48  
% 7.79/1.48  fof(f105,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f30])).
% 7.79/1.48  
% 7.79/1.48  fof(f3,axiom,(
% 7.79/1.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f42,plain,(
% 7.79/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.79/1.48    inference(nnf_transformation,[],[f3])).
% 7.79/1.48  
% 7.79/1.48  fof(f43,plain,(
% 7.79/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.79/1.48    inference(rectify,[],[f42])).
% 7.79/1.48  
% 7.79/1.48  fof(f44,plain,(
% 7.79/1.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f45,plain,(
% 7.79/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 7.79/1.48  
% 7.79/1.48  fof(f69,plain,(
% 7.79/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.79/1.48    inference(cnf_transformation,[],[f45])).
% 7.79/1.48  
% 7.79/1.48  fof(f125,plain,(
% 7.79/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.79/1.48    inference(definition_unfolding,[],[f69,f122])).
% 7.79/1.48  
% 7.79/1.48  fof(f129,plain,(
% 7.79/1.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.79/1.48    inference(equality_resolution,[],[f125])).
% 7.79/1.48  
% 7.79/1.48  fof(f130,plain,(
% 7.79/1.48    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 7.79/1.48    inference(equality_resolution,[],[f129])).
% 7.79/1.48  
% 7.79/1.48  fof(f14,axiom,(
% 7.79/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f27,plain,(
% 7.79/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.79/1.48    inference(ennf_transformation,[],[f14])).
% 7.79/1.48  
% 7.79/1.48  fof(f102,plain,(
% 7.79/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f27])).
% 7.79/1.48  
% 7.79/1.48  fof(f1,axiom,(
% 7.79/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f22,plain,(
% 7.79/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.79/1.48    inference(ennf_transformation,[],[f1])).
% 7.79/1.48  
% 7.79/1.48  fof(f38,plain,(
% 7.79/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.79/1.48    inference(nnf_transformation,[],[f22])).
% 7.79/1.48  
% 7.79/1.48  fof(f39,plain,(
% 7.79/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.79/1.48    inference(rectify,[],[f38])).
% 7.79/1.48  
% 7.79/1.48  fof(f40,plain,(
% 7.79/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f41,plain,(
% 7.79/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 7.79/1.48  
% 7.79/1.48  fof(f64,plain,(
% 7.79/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f41])).
% 7.79/1.48  
% 7.79/1.48  fof(f12,axiom,(
% 7.79/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f24,plain,(
% 7.79/1.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.79/1.48    inference(ennf_transformation,[],[f12])).
% 7.79/1.48  
% 7.79/1.48  fof(f54,plain,(
% 7.79/1.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.79/1.48    inference(nnf_transformation,[],[f24])).
% 7.79/1.48  
% 7.79/1.48  fof(f94,plain,(
% 7.79/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f54])).
% 7.79/1.48  
% 7.79/1.48  fof(f16,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f21,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.79/1.48    inference(pure_predicate_removal,[],[f16])).
% 7.79/1.48  
% 7.79/1.48  fof(f29,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f21])).
% 7.79/1.48  
% 7.79/1.48  fof(f104,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f29])).
% 7.79/1.48  
% 7.79/1.48  fof(f15,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f28,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f15])).
% 7.79/1.48  
% 7.79/1.48  fof(f103,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f28])).
% 7.79/1.48  
% 7.79/1.48  fof(f68,plain,(
% 7.79/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.79/1.48    inference(cnf_transformation,[],[f45])).
% 7.79/1.48  
% 7.79/1.48  fof(f126,plain,(
% 7.79/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.79/1.48    inference(definition_unfolding,[],[f68,f122])).
% 7.79/1.48  
% 7.79/1.48  fof(f131,plain,(
% 7.79/1.48    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 7.79/1.48    inference(equality_resolution,[],[f126])).
% 7.79/1.48  
% 7.79/1.48  fof(f116,plain,(
% 7.79/1.48    k1_funct_1(sK11,sK10) != sK9),
% 7.79/1.48    inference(cnf_transformation,[],[f63])).
% 7.79/1.48  
% 7.79/1.48  fof(f115,plain,(
% 7.79/1.48    r2_hidden(sK10,sK8)),
% 7.79/1.48    inference(cnf_transformation,[],[f63])).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2693,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.79/1.48      theory(equality) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_5616,plain,
% 7.79/1.48      ( r2_hidden(X0,X1)
% 7.79/1.48      | ~ r2_hidden(sK10,sK8)
% 7.79/1.48      | X1 != sK8
% 7.79/1.48      | X0 != sK10 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_2693]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_16930,plain,
% 7.79/1.48      ( r2_hidden(X0,k1_relat_1(sK11))
% 7.79/1.48      | ~ r2_hidden(sK10,sK8)
% 7.79/1.48      | X0 != sK10
% 7.79/1.48      | k1_relat_1(sK11) != sK8 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_5616]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_23798,plain,
% 7.79/1.48      ( r2_hidden(sK10,k1_relat_1(sK11))
% 7.79/1.48      | ~ r2_hidden(sK10,sK8)
% 7.79/1.48      | k1_relat_1(sK11) != sK8
% 7.79/1.48      | sK10 != sK10 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_16930]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_28,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.79/1.48      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.79/1.48      | ~ v1_funct_1(X1)
% 7.79/1.48      | ~ v1_relat_1(X1) ),
% 7.79/1.48      inference(cnf_transformation,[],[f142]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_45,negated_conjecture,
% 7.79/1.48      ( v1_funct_1(sK11) ),
% 7.79/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_961,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.79/1.48      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.79/1.48      | ~ v1_relat_1(X1)
% 7.79/1.48      | sK11 != X1 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_28,c_45]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_962,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k1_relat_1(sK11))
% 7.79/1.48      | r2_hidden(k1_funct_1(sK11,X0),k2_relat_1(sK11))
% 7.79/1.48      | ~ v1_relat_1(sK11) ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_961]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_13627,plain,
% 7.79/1.48      ( r2_hidden(k1_funct_1(sK11,sK10),k2_relat_1(sK11))
% 7.79/1.48      | ~ r2_hidden(sK10,k1_relat_1(sK11))
% 7.79/1.48      | ~ v1_relat_1(sK11) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_962]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3,plain,
% 7.79/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3265,plain,
% 7.79/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_44,negated_conjecture,
% 7.79/1.48      ( v1_funct_2(sK11,sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)) ),
% 7.79/1.48      inference(cnf_transformation,[],[f128]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_40,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.79/1.48      | k1_xboole_0 = X2 ),
% 7.79/1.48      inference(cnf_transformation,[],[f106]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_43,negated_conjecture,
% 7.79/1.48      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)))) ),
% 7.79/1.48      inference(cnf_transformation,[],[f127]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_635,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 7.79/1.48      | sK11 != X0
% 7.79/1.48      | k1_xboole_0 = X2 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_40,c_43]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_636,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK11,X0,X1)
% 7.79/1.48      | k1_relset_1(X0,X1,sK11) = X0
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.79/1.48      | k1_xboole_0 = X1 ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_635]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1291,plain,
% 7.79/1.48      ( k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9) != X0
% 7.79/1.48      | k1_relset_1(X1,X0,sK11) = X1
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 7.79/1.48      | sK8 != X1
% 7.79/1.48      | sK11 != sK11
% 7.79/1.48      | k1_xboole_0 = X0 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_44,c_636]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1292,plain,
% 7.79/1.48      ( k1_relset_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9),sK11) = sK8
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)))
% 7.79/1.48      | k1_xboole_0 = k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9) ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_1291]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1771,plain,
% 7.79/1.48      ( k1_relset_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9),sK11) = sK8
% 7.79/1.48      | k1_xboole_0 = k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9) ),
% 7.79/1.48      inference(equality_resolution_simp,[status(thm)],[c_1292]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_34,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_671,plain,
% 7.79/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.79/1.48      | sK11 != X2 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_34,c_43]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_672,plain,
% 7.79/1.48      ( k1_relset_1(X0,X1,sK11) = k1_relat_1(sK11)
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_671]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3483,plain,
% 7.79/1.48      ( k1_relset_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9),sK11) = k1_relat_1(sK11) ),
% 7.79/1.48      inference(equality_resolution,[status(thm)],[c_672]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3858,plain,
% 7.79/1.48      ( k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9) = k1_xboole_0
% 7.79/1.48      | k1_relat_1(sK11) = sK8 ),
% 7.79/1.48      inference(demodulation,[status(thm)],[c_1771,c_3483]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_6,plain,
% 7.79/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.79/1.48      inference(cnf_transformation,[],[f130]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3262,plain,
% 7.79/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_5987,plain,
% 7.79/1.48      ( k1_relat_1(sK11) = sK8
% 7.79/1.48      | r2_hidden(sK9,k1_xboole_0) = iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_3858,c_3262]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_31,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3245,plain,
% 7.79/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.79/1.48      | r1_tarski(X1,X0) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11022,plain,
% 7.79/1.48      ( k1_relat_1(sK11) = sK8
% 7.79/1.48      | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_5987,c_3245]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11378,plain,
% 7.79/1.48      ( k1_relat_1(sK11) = sK8 ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_3265,c_11022]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2690,plain,( X0 = X0 ),theory(equality) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_6626,plain,
% 7.79/1.48      ( sK10 = sK10 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_2690]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.79/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3377,plain,
% 7.79/1.48      ( ~ r2_hidden(k1_funct_1(sK11,sK10),X0)
% 7.79/1.48      | r2_hidden(k1_funct_1(sK11,sK10),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))
% 7.79/1.48      | ~ r1_tarski(X0,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_5418,plain,
% 7.79/1.48      ( r2_hidden(k1_funct_1(sK11,sK10),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))
% 7.79/1.48      | ~ r2_hidden(k1_funct_1(sK11,sK10),k2_relat_1(sK11))
% 7.79/1.48      | ~ r1_tarski(k2_relat_1(sK11),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_3377]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3500,plain,
% 7.79/1.48      ( k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) = k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_2690]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_24,plain,
% 7.79/1.48      ( ~ v5_relat_1(X0,X1)
% 7.79/1.48      | r1_tarski(k2_relat_1(X0),X1)
% 7.79/1.48      | ~ v1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_33,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | v5_relat_1(X0,X2) ),
% 7.79/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_490,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | r1_tarski(k2_relat_1(X3),X4)
% 7.79/1.48      | ~ v1_relat_1(X3)
% 7.79/1.48      | X0 != X3
% 7.79/1.48      | X2 != X4 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_491,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | r1_tarski(k2_relat_1(X0),X2)
% 7.79/1.48      | ~ v1_relat_1(X0) ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_490]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_32,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | v1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f103]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_495,plain,
% 7.79/1.48      ( r1_tarski(k2_relat_1(X0),X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_491,c_32]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_496,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.79/1.48      inference(renaming,[status(thm)],[c_495]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_623,plain,
% 7.79/1.48      ( r1_tarski(k2_relat_1(X0),X1)
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 7.79/1.48      | sK11 != X0 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_496,c_43]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_624,plain,
% 7.79/1.48      ( r1_tarski(k2_relat_1(sK11),X0)
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_623]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3421,plain,
% 7.79/1.48      ( r1_tarski(k2_relat_1(sK11),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_624]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_680,plain,
% 7.79/1.48      ( v1_relat_1(X0)
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 7.79/1.48      | sK11 != X0 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_32,c_43]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_681,plain,
% 7.79/1.48      ( v1_relat_1(sK11)
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_680]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3359,plain,
% 7.79/1.48      ( v1_relat_1(sK11)
% 7.79/1.48      | k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) != k1_zfmisc_1(k2_zfmisc_1(sK8,k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_681]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_7,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.79/1.48      inference(cnf_transformation,[],[f131]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3313,plain,
% 7.79/1.48      ( ~ r2_hidden(k1_funct_1(sK11,sK10),k6_enumset1(sK9,sK9,sK9,sK9,sK9,sK9,sK9,sK9))
% 7.79/1.48      | k1_funct_1(sK11,sK10) = sK9 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_41,negated_conjecture,
% 7.79/1.48      ( k1_funct_1(sK11,sK10) != sK9 ),
% 7.79/1.48      inference(cnf_transformation,[],[f116]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_42,negated_conjecture,
% 7.79/1.48      ( r2_hidden(sK10,sK8) ),
% 7.79/1.48      inference(cnf_transformation,[],[f115]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(contradiction,plain,
% 7.79/1.48      ( $false ),
% 7.79/1.48      inference(minisat,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_23798,c_13627,c_11378,c_6626,c_5418,c_3500,c_3421,
% 7.79/1.48                 c_3359,c_3313,c_41,c_42]) ).
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  ------                               Statistics
% 7.79/1.48  
% 7.79/1.48  ------ General
% 7.79/1.48  
% 7.79/1.48  abstr_ref_over_cycles:                  0
% 7.79/1.48  abstr_ref_under_cycles:                 0
% 7.79/1.48  gc_basic_clause_elim:                   0
% 7.79/1.48  forced_gc_time:                         0
% 7.79/1.48  parsing_time:                           0.008
% 7.79/1.48  unif_index_cands_time:                  0.
% 7.79/1.48  unif_index_add_time:                    0.
% 7.79/1.48  orderings_time:                         0.
% 7.79/1.48  out_proof_time:                         0.011
% 7.79/1.48  total_time:                             0.682
% 7.79/1.48  num_of_symbols:                         58
% 7.79/1.48  num_of_terms:                           29554
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing
% 7.79/1.48  
% 7.79/1.48  num_of_splits:                          0
% 7.79/1.48  num_of_split_atoms:                     0
% 7.79/1.48  num_of_reused_defs:                     0
% 7.79/1.48  num_eq_ax_congr_red:                    109
% 7.79/1.48  num_of_sem_filtered_clauses:            1
% 7.79/1.48  num_of_subtypes:                        0
% 7.79/1.48  monotx_restored_types:                  0
% 7.79/1.48  sat_num_of_epr_types:                   0
% 7.79/1.48  sat_num_of_non_cyclic_types:            0
% 7.79/1.48  sat_guarded_non_collapsed_types:        0
% 7.79/1.48  num_pure_diseq_elim:                    0
% 7.79/1.48  simp_replaced_by:                       0
% 7.79/1.48  res_preprocessed:                       195
% 7.79/1.48  prep_upred:                             0
% 7.79/1.48  prep_unflattend:                        677
% 7.79/1.48  smt_new_axioms:                         0
% 7.79/1.48  pred_elim_cands:                        5
% 7.79/1.48  pred_elim:                              4
% 7.79/1.48  pred_elim_cl:                           8
% 7.79/1.48  pred_elim_cycles:                       13
% 7.79/1.48  merged_defs:                            0
% 7.79/1.48  merged_defs_ncl:                        0
% 7.79/1.48  bin_hyper_res:                          0
% 7.79/1.48  prep_cycles:                            4
% 7.79/1.48  pred_elim_time:                         0.026
% 7.79/1.48  splitting_time:                         0.
% 7.79/1.48  sem_filter_time:                        0.
% 7.79/1.48  monotx_time:                            0.
% 7.79/1.48  subtype_inf_time:                       0.
% 7.79/1.48  
% 7.79/1.48  ------ Problem properties
% 7.79/1.48  
% 7.79/1.48  clauses:                                38
% 7.79/1.48  conjectures:                            2
% 7.79/1.48  epr:                                    15
% 7.79/1.48  horn:                                   30
% 7.79/1.48  ground:                                 5
% 7.79/1.48  unary:                                  13
% 7.79/1.48  binary:                                 9
% 7.79/1.48  lits:                                   90
% 7.79/1.48  lits_eq:                                34
% 7.79/1.48  fd_pure:                                0
% 7.79/1.48  fd_pseudo:                              0
% 7.79/1.48  fd_cond:                                3
% 7.79/1.48  fd_pseudo_cond:                         4
% 7.79/1.48  ac_symbols:                             0
% 7.79/1.48  
% 7.79/1.48  ------ Propositional Solver
% 7.79/1.48  
% 7.79/1.48  prop_solver_calls:                      30
% 7.79/1.48  prop_fast_solver_calls:                 1789
% 7.79/1.48  smt_solver_calls:                       0
% 7.79/1.48  smt_fast_solver_calls:                  0
% 7.79/1.48  prop_num_of_clauses:                    7861
% 7.79/1.48  prop_preprocess_simplified:             27988
% 7.79/1.48  prop_fo_subsumed:                       34
% 7.79/1.48  prop_solver_time:                       0.
% 7.79/1.48  smt_solver_time:                        0.
% 7.79/1.48  smt_fast_solver_time:                   0.
% 7.79/1.48  prop_fast_solver_time:                  0.
% 7.79/1.48  prop_unsat_core_time:                   0.
% 7.79/1.48  
% 7.79/1.48  ------ QBF
% 7.79/1.48  
% 7.79/1.48  qbf_q_res:                              0
% 7.79/1.48  qbf_num_tautologies:                    0
% 7.79/1.48  qbf_prep_cycles:                        0
% 7.79/1.48  
% 7.79/1.48  ------ BMC1
% 7.79/1.48  
% 7.79/1.48  bmc1_current_bound:                     -1
% 7.79/1.48  bmc1_last_solved_bound:                 -1
% 7.79/1.48  bmc1_unsat_core_size:                   -1
% 7.79/1.48  bmc1_unsat_core_parents_size:           -1
% 7.79/1.48  bmc1_merge_next_fun:                    0
% 7.79/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.79/1.48  
% 7.79/1.48  ------ Instantiation
% 7.79/1.48  
% 7.79/1.48  inst_num_of_clauses:                    2509
% 7.79/1.48  inst_num_in_passive:                    1944
% 7.79/1.48  inst_num_in_active:                     518
% 7.79/1.48  inst_num_in_unprocessed:                46
% 7.79/1.48  inst_num_of_loops:                      672
% 7.79/1.48  inst_num_of_learning_restarts:          0
% 7.79/1.48  inst_num_moves_active_passive:          153
% 7.79/1.48  inst_lit_activity:                      0
% 7.79/1.48  inst_lit_activity_moves:                0
% 7.79/1.48  inst_num_tautologies:                   0
% 7.79/1.48  inst_num_prop_implied:                  0
% 7.79/1.48  inst_num_existing_simplified:           0
% 7.79/1.48  inst_num_eq_res_simplified:             0
% 7.79/1.48  inst_num_child_elim:                    0
% 7.79/1.48  inst_num_of_dismatching_blockings:      1052
% 7.79/1.48  inst_num_of_non_proper_insts:           2322
% 7.79/1.48  inst_num_of_duplicates:                 0
% 7.79/1.48  inst_inst_num_from_inst_to_res:         0
% 7.79/1.48  inst_dismatching_checking_time:         0.
% 7.79/1.48  
% 7.79/1.48  ------ Resolution
% 7.79/1.48  
% 7.79/1.48  res_num_of_clauses:                     0
% 7.79/1.48  res_num_in_passive:                     0
% 7.79/1.48  res_num_in_active:                      0
% 7.79/1.48  res_num_of_loops:                       199
% 7.79/1.48  res_forward_subset_subsumed:            865
% 7.79/1.48  res_backward_subset_subsumed:           0
% 7.79/1.48  res_forward_subsumed:                   0
% 7.79/1.48  res_backward_subsumed:                  1
% 7.79/1.48  res_forward_subsumption_resolution:     0
% 7.79/1.48  res_backward_subsumption_resolution:    0
% 7.79/1.48  res_clause_to_clause_subsumption:       2644
% 7.79/1.48  res_orphan_elimination:                 0
% 7.79/1.48  res_tautology_del:                      224
% 7.79/1.48  res_num_eq_res_simplified:              1
% 7.79/1.48  res_num_sel_changes:                    0
% 7.79/1.48  res_moves_from_active_to_pass:          0
% 7.79/1.48  
% 7.79/1.48  ------ Superposition
% 7.79/1.48  
% 7.79/1.48  sup_time_total:                         0.
% 7.79/1.48  sup_time_generating:                    0.
% 7.79/1.48  sup_time_sim_full:                      0.
% 7.79/1.48  sup_time_sim_immed:                     0.
% 7.79/1.48  
% 7.79/1.48  sup_num_of_clauses:                     348
% 7.79/1.48  sup_num_in_active:                      102
% 7.79/1.48  sup_num_in_passive:                     246
% 7.79/1.48  sup_num_of_loops:                       134
% 7.79/1.48  sup_fw_superposition:                   237
% 7.79/1.48  sup_bw_superposition:                   274
% 7.79/1.48  sup_immediate_simplified:               29
% 7.79/1.48  sup_given_eliminated:                   0
% 7.79/1.48  comparisons_done:                       0
% 7.79/1.48  comparisons_avoided:                    80
% 7.79/1.48  
% 7.79/1.48  ------ Simplifications
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  sim_fw_subset_subsumed:                 13
% 7.79/1.48  sim_bw_subset_subsumed:                 20
% 7.79/1.48  sim_fw_subsumed:                        3
% 7.79/1.48  sim_bw_subsumed:                        3
% 7.79/1.48  sim_fw_subsumption_res:                 0
% 7.79/1.48  sim_bw_subsumption_res:                 0
% 7.79/1.48  sim_tautology_del:                      0
% 7.79/1.48  sim_eq_tautology_del:                   121
% 7.79/1.48  sim_eq_res_simp:                        0
% 7.79/1.48  sim_fw_demodulated:                     1
% 7.79/1.48  sim_bw_demodulated:                     26
% 7.79/1.48  sim_light_normalised:                   15
% 7.79/1.48  sim_joinable_taut:                      0
% 7.79/1.48  sim_joinable_simp:                      0
% 7.79/1.48  sim_ac_normalised:                      0
% 7.79/1.48  sim_smt_subsumption:                    0
% 7.79/1.48  
%------------------------------------------------------------------------------

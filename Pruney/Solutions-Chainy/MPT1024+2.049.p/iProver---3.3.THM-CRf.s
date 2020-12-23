%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:57 EST 2020

% Result     : Theorem 19.68s
% Output     : CNFRefutation 19.68s
% Verified   : 
% Statistics : Number of formulae       :  291 (53217 expanded)
%              Number of clauses        :  207 (17918 expanded)
%              Number of leaves         :   28 (12643 expanded)
%              Depth                    :   44
%              Number of atoms          : 1007 (263220 expanded)
%              Number of equality atoms :  560 (66583 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK10
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK10,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK9,X5) != X4
              | ~ r2_hidden(X5,sK8)
              | ~ r2_hidden(X5,sK6) )
          & r2_hidden(X4,k7_relset_1(sK6,sK7,sK9,sK8)) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK9,sK6,sK7)
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ! [X5] :
        ( k1_funct_1(sK9,X5) != sK10
        | ~ r2_hidden(X5,sK8)
        | ~ r2_hidden(X5,sK6) )
    & r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK9,sK6,sK7)
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f30,f50,f49])).

fof(f85,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
    inference(cnf_transformation,[],[f51])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ! [X5] :
      ( k1_funct_1(sK9,X5) != sK10
      | ~ r2_hidden(X5,sK8)
      | ~ r2_hidden(X5,sK6) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK1(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2)
                  & r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
                    & r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f39,f38,f37])).

fof(f62,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f43])).

fof(f46,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK5(X1,X2),X6),X2)
        & r2_hidden(sK5(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK5(X1,X2),X6),X2)
            & r2_hidden(sK5(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f46,f45])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK5(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f75,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | ~ r2_hidden(k4_tarski(sK5(X1,X2),X6),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f61,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f97,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_934,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_907,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_910,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1453,plain,
    ( k1_relset_1(sK6,sK7,sK9) = sK6
    | sK7 = k1_xboole_0
    | v1_funct_2(sK9,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_907,c_910])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1469,plain,
    ( ~ v1_funct_2(sK9,sK6,sK7)
    | k1_relset_1(sK6,sK7,sK9) = sK6
    | sK7 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1453])).

cnf(c_2014,plain,
    ( sK7 = k1_xboole_0
    | k1_relset_1(sK6,sK7,sK9) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1453,c_34,c_1469])).

cnf(c_2015,plain,
    ( k1_relset_1(sK6,sK7,sK9) = sK6
    | sK7 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2014])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_920,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1474,plain,
    ( k1_relset_1(sK6,sK7,sK9) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_907,c_920])).

cnf(c_2016,plain,
    ( k1_relat_1(sK9) = sK6
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2015,c_1474])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_932,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3265,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_932])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1333,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK6,sK7))
    | v1_relat_1(sK9) ),
    inference(resolution,[status(thm)],[c_3,c_33])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1361,plain,
    ( v1_relat_1(sK9) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1333,c_4])).

cnf(c_1362,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_3887,plain,
    ( r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3265,c_1362])).

cnf(c_3888,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_3887])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_919,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1592,plain,
    ( k7_relset_1(sK6,sK7,sK9,X0) = k9_relat_1(sK9,X0) ),
    inference(superposition,[status(thm)],[c_907,c_919])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_908,plain,
    ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1878,plain,
    ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1592,c_908])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_933,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_922,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3513,plain,
    ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
    | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_922])).

cnf(c_10928,plain,
    ( k1_funct_1(sK9,sK0(sK10,sK8,sK9)) = sK10
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_3513])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11472,plain,
    ( k1_funct_1(sK9,sK0(sK10,sK8,sK9)) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10928,c_36,c_1362])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X0,sK8)
    | k1_funct_1(sK9,X0) != sK10 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_909,plain,
    ( k1_funct_1(sK9,X0) != sK10
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11477,plain,
    ( r2_hidden(sK0(sK10,sK8,sK9),sK6) != iProver_top
    | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_11472,c_909])).

cnf(c_11726,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3888,c_11477])).

cnf(c_11744,plain,
    ( r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11726,c_1878])).

cnf(c_11745,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_11744])).

cnf(c_11750,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_11745])).

cnf(c_12039,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11750,c_1362,c_1878])).

cnf(c_12075,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12039,c_907])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_914,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12470,plain,
    ( sK6 = k1_xboole_0
    | sK9 = k1_xboole_0
    | v1_funct_2(sK9,sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12075,c_914])).

cnf(c_37,plain,
    ( v1_funct_2(sK9,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_331,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_358,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_1564,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_332,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1947,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_1948,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_344,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1422,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK9,sK6,sK7)
    | X2 != sK7
    | X1 != sK6
    | X0 != sK9 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_1563,plain,
    ( v1_funct_2(sK9,X0,X1)
    | ~ v1_funct_2(sK9,sK6,sK7)
    | X1 != sK7
    | X0 != sK6
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_2473,plain,
    ( v1_funct_2(sK9,sK6,X0)
    | ~ v1_funct_2(sK9,sK6,sK7)
    | X0 != sK7
    | sK6 != sK6
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_2475,plain,
    ( X0 != sK7
    | sK6 != sK6
    | sK9 != sK9
    | v1_funct_2(sK9,sK6,X0) = iProver_top
    | v1_funct_2(sK9,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2473])).

cnf(c_2477,plain,
    ( sK6 != sK6
    | sK9 != sK9
    | k1_xboole_0 != sK7
    | v1_funct_2(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2475])).

cnf(c_2474,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_12876,plain,
    ( sK9 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12470,c_37,c_358,c_1362,c_1564,c_1878,c_1948,c_2477,c_2474,c_11750])).

cnf(c_12877,plain,
    ( sK6 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_12876])).

cnf(c_12881,plain,
    ( sK9 = k1_xboole_0
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12877,c_12075])).

cnf(c_338,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_350,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1265,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1266,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_1268,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1518,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1519,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_1521,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1346,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_2194,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_4186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_2194])).

cnf(c_4187,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK9 != X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4186])).

cnf(c_4189,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK9 != k1_xboole_0
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4187])).

cnf(c_335,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_9524,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) != k2_zfmisc_1(X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_9525,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9524])).

cnf(c_13542,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12881,c_350,c_358,c_1268,c_1521,c_4189,c_9525])).

cnf(c_13552,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK9) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_13542,c_920])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_911,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13554,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK9) = k1_xboole_0
    | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13542,c_911])).

cnf(c_13560,plain,
    ( k1_relat_1(sK9) = k1_xboole_0
    | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13552,c_13554])).

cnf(c_2325,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK9,X3,k1_xboole_0)
    | X3 != X1
    | sK9 != X0
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_2326,plain,
    ( X0 != X1
    | sK9 != X2
    | k1_xboole_0 != X3
    | v1_funct_2(X2,X1,X3) != iProver_top
    | v1_funct_2(sK9,X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2325])).

cnf(c_2328,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2326])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2427,plain,
    ( r2_hidden(sK3(sK9,X0,sK10),X0)
    | ~ r2_hidden(sK10,k9_relat_1(sK9,X0))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_24422,plain,
    ( r2_hidden(sK3(sK9,sK8,sK10),sK8)
    | ~ r2_hidden(sK10,k9_relat_1(sK9,sK8))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_24425,plain,
    ( r2_hidden(sK3(sK9,sK8,sK10),sK8) = iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24422])).

cnf(c_905,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_940,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK5(X1,X0),X1)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_916,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK5(X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2584,plain,
    ( k1_relset_1(sK6,sK7,sK9) = sK6
    | r2_hidden(sK5(sK6,sK9),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_907,c_916])).

cnf(c_2587,plain,
    ( k1_relat_1(sK9) = sK6
    | r2_hidden(sK5(sK6,sK9),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2584,c_1474])).

cnf(c_938,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_939,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2344,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_939])).

cnf(c_3045,plain,
    ( k1_relat_1(sK9) = sK6
    | r2_hidden(sK5(sK6,sK9),X0) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2587,c_2344])).

cnf(c_3864,plain,
    ( k1_relat_1(sK9) = sK6
    | r2_hidden(sK5(sK6,sK9),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3045,c_2344])).

cnf(c_4311,plain,
    ( k1_relat_1(sK9) = sK6
    | r2_hidden(sK5(sK6,sK9),X0) = iProver_top
    | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_940,c_3864])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_926,plain,
    ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7859,plain,
    ( k1_funct_1(X0,sK3(X0,X1,sK5(sK6,sK9))) = sK5(sK6,sK9)
    | k1_relat_1(sK9) = sK6
    | r1_tarski(sK6,k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4311,c_926])).

cnf(c_24697,plain,
    ( k1_funct_1(X0,sK3(X0,X1,sK5(sK6,sK9))) = sK5(sK6,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12877,c_7859])).

cnf(c_129,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_131,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_24793,plain,
    ( sK9 = k1_xboole_0
    | k1_relat_1(sK9) = sK6
    | k1_funct_1(X0,sK3(X0,X1,sK5(sK6,sK9))) = sK5(sK6,sK9)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24697,c_131])).

cnf(c_24794,plain,
    ( k1_funct_1(X0,sK3(X0,X1,sK5(sK6,sK9))) = sK5(sK6,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_24793])).

cnf(c_24804,plain,
    ( k1_funct_1(sK9,sK3(sK9,X0,sK5(sK6,sK9))) = sK5(sK6,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_24794])).

cnf(c_24805,plain,
    ( ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,sK3(sK9,X0,sK5(sK6,sK9))) = sK5(sK6,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_24804])).

cnf(c_25013,plain,
    ( sK9 = k1_xboole_0
    | k1_relat_1(sK9) = sK6
    | k1_funct_1(sK9,sK3(sK9,X0,sK5(sK6,sK9))) = sK5(sK6,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24804,c_1362])).

cnf(c_25014,plain,
    ( k1_funct_1(sK9,sK3(sK9,X0,sK5(sK6,sK9))) = sK5(sK6,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_25013])).

cnf(c_25019,plain,
    ( k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(sK6,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12877,c_25014])).

cnf(c_12884,plain,
    ( k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | r2_hidden(sK5(k1_xboole_0,sK9),X0) = iProver_top
    | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12877,c_4311])).

cnf(c_12887,plain,
    ( k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | r2_hidden(sK5(k1_xboole_0,sK9),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12877,c_2587])).

cnf(c_17263,plain,
    ( k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | r2_hidden(sK5(k1_xboole_0,sK9),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12887,c_2344])).

cnf(c_17427,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK9),X0) = iProver_top
    | sK9 = k1_xboole_0
    | k1_relat_1(sK9) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12884,c_129,c_17263])).

cnf(c_17428,plain,
    ( k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | r2_hidden(sK5(k1_xboole_0,sK9),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_17427])).

cnf(c_17435,plain,
    ( k1_funct_1(X0,sK3(X0,X1,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17428,c_926])).

cnf(c_20031,plain,
    ( k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_17435])).

cnf(c_20032,plain,
    ( ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_20031])).

cnf(c_20113,plain,
    ( sK9 = k1_xboole_0
    | k1_relat_1(sK9) = sK6
    | k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20031,c_1361,c_20032])).

cnf(c_20114,plain,
    ( k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_20113])).

cnf(c_25212,plain,
    ( sK5(k1_xboole_0,sK9) = sK5(sK6,sK9)
    | k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25019,c_20114])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_923,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(sK5(X1,X0),X3),X0)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_917,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(k4_tarski(sK5(X0,X2),X3),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4493,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK5(X0,X2),k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_917])).

cnf(c_28719,plain,
    ( k1_relset_1(sK6,k1_xboole_0,sK9) = sK6
    | r2_hidden(sK5(sK6,sK9),k1_relat_1(sK9)) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_12075,c_4493])).

cnf(c_12074,plain,
    ( k1_relset_1(sK6,k1_xboole_0,sK9) = k1_relat_1(sK9) ),
    inference(demodulation,[status(thm)],[c_12039,c_1474])).

cnf(c_28724,plain,
    ( k1_relat_1(sK9) = sK6
    | r2_hidden(sK5(sK6,sK9),k1_relat_1(sK9)) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28719,c_12074])).

cnf(c_29120,plain,
    ( k1_relat_1(sK9) = sK6
    | r2_hidden(sK5(sK6,sK9),k1_relat_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28724,c_36,c_1362])).

cnf(c_29128,plain,
    ( k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0
    | r2_hidden(sK5(k1_xboole_0,sK9),k1_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25212,c_29120])).

cnf(c_29405,plain,
    ( k1_relat_1(sK9) = sK6
    | sK9 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29128,c_17428])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_924,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_29406,plain,
    ( sK9 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK3(sK9,X1,X0),sK6) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_29405,c_924])).

cnf(c_31089,plain,
    ( sK9 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK3(sK9,X1,X0),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29406,c_36,c_1362])).

cnf(c_4792,plain,
    ( k1_funct_1(sK9,sK3(sK9,sK8,sK10)) = sK10
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_926])).

cnf(c_5118,plain,
    ( k1_funct_1(sK9,sK3(sK9,sK8,sK10)) = sK10 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4792,c_36,c_1362])).

cnf(c_5122,plain,
    ( r2_hidden(sK3(sK9,sK8,sK10),sK6) != iProver_top
    | r2_hidden(sK3(sK9,sK8,sK10),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5118,c_909])).

cnf(c_31100,plain,
    ( sK9 = k1_xboole_0
    | r2_hidden(sK3(sK9,sK8,sK10),sK8) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31089,c_5122])).

cnf(c_29407,plain,
    ( sK9 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_29405,c_932])).

cnf(c_30786,plain,
    ( r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | sK9 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29407,c_1362])).

cnf(c_30787,plain,
    ( sK9 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_30786])).

cnf(c_30798,plain,
    ( sK9 = k1_xboole_0
    | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30787,c_11477])).

cnf(c_31532,plain,
    ( sK9 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30798,c_36,c_1362,c_1878,c_24425,c_31100])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_913,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13586,plain,
    ( k1_relat_1(sK9) != k1_xboole_0
    | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13552,c_913])).

cnf(c_14420,plain,
    ( v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) = iProver_top
    | k1_relat_1(sK9) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13586,c_350,c_358,c_1268,c_1521,c_4189,c_9525,c_12881])).

cnf(c_14421,plain,
    ( k1_relat_1(sK9) != k1_xboole_0
    | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_14420])).

cnf(c_31597,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_31532,c_14421])).

cnf(c_52,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_54,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_121,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_123,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_1270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1271,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_1273,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_341,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1300,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | X0 != sK9 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1301,plain,
    ( X0 != sK9
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1300])).

cnf(c_1303,plain,
    ( k1_xboole_0 != sK9
    | v1_funct_1(sK9) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_1516,plain,
    ( X0 != X1
    | X0 = sK9
    | sK9 != X1 ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_1517,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_4565,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4493])).

cnf(c_4665,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r2_hidden(sK5(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_27,c_24])).

cnf(c_4666,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r2_hidden(sK5(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4665])).

cnf(c_4668,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4666])).

cnf(c_2706,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK5(X0,X2),X0)
    | r2_hidden(sK5(X0,X2),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5173,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1)))
    | ~ r2_hidden(sK5(X0,X2),X0)
    | r2_hidden(sK5(X0,X2),k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_2706])).

cnf(c_5175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1))) != iProver_top
    | r2_hidden(sK5(X0,X2),X0) != iProver_top
    | r2_hidden(sK5(X0,X2),k1_relat_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5173])).

cnf(c_5177,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) != iProver_top
    | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
    | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5175])).

cnf(c_9321,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1)))
    | ~ r1_tarski(X0,k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9322,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9321])).

cnf(c_9324,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9322])).

cnf(c_21034,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_21037,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21034])).

cnf(c_21039,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_21037])).

cnf(c_36671,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31597,c_36,c_54,c_123,c_358,c_1268,c_1273,c_1303,c_1362,c_1517,c_1521,c_1878,c_4565,c_4668,c_5177,c_9324,c_21039,c_24425,c_31100])).

cnf(c_72441,plain,
    ( k1_relat_1(sK9) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13560,c_36,c_54,c_123,c_358,c_1268,c_1273,c_1303,c_1362,c_1517,c_1521,c_1878,c_2328,c_4565,c_4668,c_5177,c_9324,c_21039,c_24425,c_31100])).

cnf(c_72443,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_72441,c_31532])).

cnf(c_3266,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X3) = iProver_top
    | r1_tarski(k1_relat_1(X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_2344])).

cnf(c_12586,plain,
    ( r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
    | r1_tarski(k1_relat_1(sK9),sK6) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3266,c_11477])).

cnf(c_13393,plain,
    ( r1_tarski(k1_relat_1(sK9),sK6) != iProver_top
    | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12586,c_1362,c_1878])).

cnf(c_13394,plain,
    ( r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top
    | r1_tarski(k1_relat_1(sK9),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_13393])).

cnf(c_13399,plain,
    ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
    | r1_tarski(k1_relat_1(sK9),sK6) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_13394])).

cnf(c_14131,plain,
    ( r1_tarski(k1_relat_1(sK9),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13399,c_1362,c_1878])).

cnf(c_31598,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31532,c_14131])).

cnf(c_72483,plain,
    ( r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_72443,c_31598])).

cnf(c_74962,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_72483,c_940])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:47:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 19.68/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.68/3.00  
% 19.68/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.68/3.00  
% 19.68/3.00  ------  iProver source info
% 19.68/3.00  
% 19.68/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.68/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.68/3.00  git: non_committed_changes: false
% 19.68/3.00  git: last_make_outside_of_git: false
% 19.68/3.00  
% 19.68/3.00  ------ 
% 19.68/3.00  ------ Parsing...
% 19.68/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.68/3.00  
% 19.68/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.68/3.00  
% 19.68/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.68/3.00  
% 19.68/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.68/3.00  ------ Proving...
% 19.68/3.00  ------ Problem Properties 
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  clauses                                 36
% 19.68/3.00  conjectures                             5
% 19.68/3.00  EPR                                     3
% 19.68/3.00  Horn                                    28
% 19.68/3.00  unary                                   6
% 19.68/3.00  binary                                  3
% 19.68/3.00  lits                                    117
% 19.68/3.00  lits eq                                 23
% 19.68/3.00  fd_pure                                 0
% 19.68/3.00  fd_pseudo                               0
% 19.68/3.00  fd_cond                                 3
% 19.68/3.00  fd_pseudo_cond                          5
% 19.68/3.00  AC symbols                              0
% 19.68/3.00  
% 19.68/3.00  ------ Input Options Time Limit: Unbounded
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  ------ 
% 19.68/3.00  Current options:
% 19.68/3.00  ------ 
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  ------ Proving...
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  % SZS status Theorem for theBenchmark.p
% 19.68/3.00  
% 19.68/3.00   Resolution empty clause
% 19.68/3.00  
% 19.68/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.68/3.00  
% 19.68/3.00  fof(f6,axiom,(
% 19.68/3.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f19,plain,(
% 19.68/3.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 19.68/3.00    inference(ennf_transformation,[],[f6])).
% 19.68/3.00  
% 19.68/3.00  fof(f31,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.68/3.00    inference(nnf_transformation,[],[f19])).
% 19.68/3.00  
% 19.68/3.00  fof(f32,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.68/3.00    inference(rectify,[],[f31])).
% 19.68/3.00  
% 19.68/3.00  fof(f33,plain,(
% 19.68/3.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 19.68/3.00    introduced(choice_axiom,[])).
% 19.68/3.00  
% 19.68/3.00  fof(f34,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.68/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 19.68/3.00  
% 19.68/3.00  fof(f59,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f34])).
% 19.68/3.00  
% 19.68/3.00  fof(f13,conjecture,(
% 19.68/3.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f14,negated_conjecture,(
% 19.68/3.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 19.68/3.00    inference(negated_conjecture,[],[f13])).
% 19.68/3.00  
% 19.68/3.00  fof(f29,plain,(
% 19.68/3.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 19.68/3.00    inference(ennf_transformation,[],[f14])).
% 19.68/3.00  
% 19.68/3.00  fof(f30,plain,(
% 19.68/3.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 19.68/3.00    inference(flattening,[],[f29])).
% 19.68/3.00  
% 19.68/3.00  fof(f50,plain,(
% 19.68/3.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK10 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK10,k7_relset_1(X0,X1,X3,X2)))) )),
% 19.68/3.00    introduced(choice_axiom,[])).
% 19.68/3.00  
% 19.68/3.00  fof(f49,plain,(
% 19.68/3.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK9,X5) != X4 | ~r2_hidden(X5,sK8) | ~r2_hidden(X5,sK6)) & r2_hidden(X4,k7_relset_1(sK6,sK7,sK9,sK8))) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK9,sK6,sK7) & v1_funct_1(sK9))),
% 19.68/3.00    introduced(choice_axiom,[])).
% 19.68/3.00  
% 19.68/3.00  fof(f51,plain,(
% 19.68/3.00    (! [X5] : (k1_funct_1(sK9,X5) != sK10 | ~r2_hidden(X5,sK8) | ~r2_hidden(X5,sK6)) & r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK9,sK6,sK7) & v1_funct_1(sK9)),
% 19.68/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f30,f50,f49])).
% 19.68/3.00  
% 19.68/3.00  fof(f85,plain,(
% 19.68/3.00    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 19.68/3.00    inference(cnf_transformation,[],[f51])).
% 19.68/3.00  
% 19.68/3.00  fof(f12,axiom,(
% 19.68/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f27,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.00    inference(ennf_transformation,[],[f12])).
% 19.68/3.00  
% 19.68/3.00  fof(f28,plain,(
% 19.68/3.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.00    inference(flattening,[],[f27])).
% 19.68/3.00  
% 19.68/3.00  fof(f48,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.00    inference(nnf_transformation,[],[f28])).
% 19.68/3.00  
% 19.68/3.00  fof(f77,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f48])).
% 19.68/3.00  
% 19.68/3.00  fof(f84,plain,(
% 19.68/3.00    v1_funct_2(sK9,sK6,sK7)),
% 19.68/3.00    inference(cnf_transformation,[],[f51])).
% 19.68/3.00  
% 19.68/3.00  fof(f9,axiom,(
% 19.68/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f24,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.00    inference(ennf_transformation,[],[f9])).
% 19.68/3.00  
% 19.68/3.00  fof(f72,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f24])).
% 19.68/3.00  
% 19.68/3.00  fof(f57,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f34])).
% 19.68/3.00  
% 19.68/3.00  fof(f4,axiom,(
% 19.68/3.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f18,plain,(
% 19.68/3.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 19.68/3.00    inference(ennf_transformation,[],[f4])).
% 19.68/3.00  
% 19.68/3.00  fof(f55,plain,(
% 19.68/3.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f18])).
% 19.68/3.00  
% 19.68/3.00  fof(f5,axiom,(
% 19.68/3.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f56,plain,(
% 19.68/3.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f5])).
% 19.68/3.00  
% 19.68/3.00  fof(f10,axiom,(
% 19.68/3.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f25,plain,(
% 19.68/3.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.68/3.00    inference(ennf_transformation,[],[f10])).
% 19.68/3.00  
% 19.68/3.00  fof(f73,plain,(
% 19.68/3.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f25])).
% 19.68/3.00  
% 19.68/3.00  fof(f86,plain,(
% 19.68/3.00    r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))),
% 19.68/3.00    inference(cnf_transformation,[],[f51])).
% 19.68/3.00  
% 19.68/3.00  fof(f58,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f34])).
% 19.68/3.00  
% 19.68/3.00  fof(f8,axiom,(
% 19.68/3.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f22,plain,(
% 19.68/3.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 19.68/3.00    inference(ennf_transformation,[],[f8])).
% 19.68/3.00  
% 19.68/3.00  fof(f23,plain,(
% 19.68/3.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.68/3.00    inference(flattening,[],[f22])).
% 19.68/3.00  
% 19.68/3.00  fof(f41,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.68/3.00    inference(nnf_transformation,[],[f23])).
% 19.68/3.00  
% 19.68/3.00  fof(f42,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.68/3.00    inference(flattening,[],[f41])).
% 19.68/3.00  
% 19.68/3.00  fof(f70,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f42])).
% 19.68/3.00  
% 19.68/3.00  fof(f83,plain,(
% 19.68/3.00    v1_funct_1(sK9)),
% 19.68/3.00    inference(cnf_transformation,[],[f51])).
% 19.68/3.00  
% 19.68/3.00  fof(f87,plain,(
% 19.68/3.00    ( ! [X5] : (k1_funct_1(sK9,X5) != sK10 | ~r2_hidden(X5,sK8) | ~r2_hidden(X5,sK6)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f51])).
% 19.68/3.00  
% 19.68/3.00  fof(f81,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f48])).
% 19.68/3.00  
% 19.68/3.00  fof(f96,plain,(
% 19.68/3.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 19.68/3.00    inference(equality_resolution,[],[f81])).
% 19.68/3.00  
% 19.68/3.00  fof(f3,axiom,(
% 19.68/3.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f15,plain,(
% 19.68/3.00    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 19.68/3.00    inference(unused_predicate_definition_removal,[],[f3])).
% 19.68/3.00  
% 19.68/3.00  fof(f17,plain,(
% 19.68/3.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 19.68/3.00    inference(ennf_transformation,[],[f15])).
% 19.68/3.00  
% 19.68/3.00  fof(f54,plain,(
% 19.68/3.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f17])).
% 19.68/3.00  
% 19.68/3.00  fof(f1,axiom,(
% 19.68/3.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f52,plain,(
% 19.68/3.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f1])).
% 19.68/3.00  
% 19.68/3.00  fof(f78,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f48])).
% 19.68/3.00  
% 19.68/3.00  fof(f98,plain,(
% 19.68/3.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 19.68/3.00    inference(equality_resolution,[],[f78])).
% 19.68/3.00  
% 19.68/3.00  fof(f7,axiom,(
% 19.68/3.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f20,plain,(
% 19.68/3.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.68/3.00    inference(ennf_transformation,[],[f7])).
% 19.68/3.00  
% 19.68/3.00  fof(f21,plain,(
% 19.68/3.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.68/3.00    inference(flattening,[],[f20])).
% 19.68/3.00  
% 19.68/3.00  fof(f35,plain,(
% 19.68/3.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.68/3.00    inference(nnf_transformation,[],[f21])).
% 19.68/3.00  
% 19.68/3.00  fof(f36,plain,(
% 19.68/3.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.68/3.00    inference(rectify,[],[f35])).
% 19.68/3.00  
% 19.68/3.00  fof(f39,plain,(
% 19.68/3.00    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 19.68/3.00    introduced(choice_axiom,[])).
% 19.68/3.00  
% 19.68/3.00  fof(f38,plain,(
% 19.68/3.00    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 19.68/3.00    introduced(choice_axiom,[])).
% 19.68/3.00  
% 19.68/3.00  fof(f37,plain,(
% 19.68/3.00    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 19.68/3.00    introduced(choice_axiom,[])).
% 19.68/3.00  
% 19.68/3.00  fof(f40,plain,(
% 19.68/3.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.68/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f39,f38,f37])).
% 19.68/3.00  
% 19.68/3.00  fof(f62,plain,(
% 19.68/3.00    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f40])).
% 19.68/3.00  
% 19.68/3.00  fof(f91,plain,(
% 19.68/3.00    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.00    inference(equality_resolution,[],[f62])).
% 19.68/3.00  
% 19.68/3.00  fof(f11,axiom,(
% 19.68/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f26,plain,(
% 19.68/3.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 19.68/3.00    inference(ennf_transformation,[],[f11])).
% 19.68/3.00  
% 19.68/3.00  fof(f43,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 19.68/3.00    inference(nnf_transformation,[],[f26])).
% 19.68/3.00  
% 19.68/3.00  fof(f44,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 19.68/3.00    inference(rectify,[],[f43])).
% 19.68/3.00  
% 19.68/3.00  fof(f46,plain,(
% 19.68/3.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK5(X1,X2),X6),X2) & r2_hidden(sK5(X1,X2),X1)))),
% 19.68/3.00    introduced(choice_axiom,[])).
% 19.68/3.00  
% 19.68/3.00  fof(f45,plain,(
% 19.68/3.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2))),
% 19.68/3.00    introduced(choice_axiom,[])).
% 19.68/3.00  
% 19.68/3.00  fof(f47,plain,(
% 19.68/3.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK5(X1,X2),X6),X2) & r2_hidden(sK5(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 19.68/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f46,f45])).
% 19.68/3.00  
% 19.68/3.00  fof(f74,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK5(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f47])).
% 19.68/3.00  
% 19.68/3.00  fof(f2,axiom,(
% 19.68/3.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 19.68/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.68/3.00  
% 19.68/3.00  fof(f16,plain,(
% 19.68/3.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.68/3.00    inference(ennf_transformation,[],[f2])).
% 19.68/3.00  
% 19.68/3.00  fof(f53,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f16])).
% 19.68/3.00  
% 19.68/3.00  fof(f63,plain,(
% 19.68/3.00    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f40])).
% 19.68/3.00  
% 19.68/3.00  fof(f90,plain,(
% 19.68/3.00    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.00    inference(equality_resolution,[],[f63])).
% 19.68/3.00  
% 19.68/3.00  fof(f71,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f42])).
% 19.68/3.00  
% 19.68/3.00  fof(f93,plain,(
% 19.68/3.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.68/3.00    inference(equality_resolution,[],[f71])).
% 19.68/3.00  
% 19.68/3.00  fof(f75,plain,(
% 19.68/3.00    ( ! [X6,X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | ~r2_hidden(k4_tarski(sK5(X1,X2),X6),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f47])).
% 19.68/3.00  
% 19.68/3.00  fof(f61,plain,(
% 19.68/3.00    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.00    inference(cnf_transformation,[],[f40])).
% 19.68/3.00  
% 19.68/3.00  fof(f92,plain,(
% 19.68/3.00    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.68/3.00    inference(equality_resolution,[],[f61])).
% 19.68/3.00  
% 19.68/3.00  fof(f80,plain,(
% 19.68/3.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.68/3.00    inference(cnf_transformation,[],[f48])).
% 19.68/3.00  
% 19.68/3.00  fof(f97,plain,(
% 19.68/3.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 19.68/3.00    inference(equality_resolution,[],[f80])).
% 19.68/3.00  
% 19.68/3.00  cnf(c_6,plain,
% 19.68/3.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 19.68/3.00      | r2_hidden(sK0(X0,X2,X1),X2)
% 19.68/3.00      | ~ v1_relat_1(X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f59]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_934,plain,
% 19.68/3.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 19.68/3.00      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 19.68/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_33,negated_conjecture,
% 19.68/3.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 19.68/3.00      inference(cnf_transformation,[],[f85]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_907,plain,
% 19.68/3.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_30,plain,
% 19.68/3.00      ( ~ v1_funct_2(X0,X1,X2)
% 19.68/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.00      | k1_relset_1(X1,X2,X0) = X1
% 19.68/3.00      | k1_xboole_0 = X2 ),
% 19.68/3.00      inference(cnf_transformation,[],[f77]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_910,plain,
% 19.68/3.00      ( k1_relset_1(X0,X1,X2) = X0
% 19.68/3.00      | k1_xboole_0 = X1
% 19.68/3.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 19.68/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1453,plain,
% 19.68/3.00      ( k1_relset_1(sK6,sK7,sK9) = sK6
% 19.68/3.00      | sK7 = k1_xboole_0
% 19.68/3.00      | v1_funct_2(sK9,sK6,sK7) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_907,c_910]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_34,negated_conjecture,
% 19.68/3.00      ( v1_funct_2(sK9,sK6,sK7) ),
% 19.68/3.00      inference(cnf_transformation,[],[f84]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1469,plain,
% 19.68/3.00      ( ~ v1_funct_2(sK9,sK6,sK7)
% 19.68/3.00      | k1_relset_1(sK6,sK7,sK9) = sK6
% 19.68/3.00      | sK7 = k1_xboole_0 ),
% 19.68/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_1453]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2014,plain,
% 19.68/3.00      ( sK7 = k1_xboole_0 | k1_relset_1(sK6,sK7,sK9) = sK6 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_1453,c_34,c_1469]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2015,plain,
% 19.68/3.00      ( k1_relset_1(sK6,sK7,sK9) = sK6 | sK7 = k1_xboole_0 ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_2014]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_20,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 19.68/3.00      inference(cnf_transformation,[],[f72]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_920,plain,
% 19.68/3.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 19.68/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1474,plain,
% 19.68/3.00      ( k1_relset_1(sK6,sK7,sK9) = k1_relat_1(sK9) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_907,c_920]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2016,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6 | sK7 = k1_xboole_0 ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_2015,c_1474]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_8,plain,
% 19.68/3.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 19.68/3.00      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 19.68/3.00      | ~ v1_relat_1(X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f57]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_932,plain,
% 19.68/3.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 19.68/3.00      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 19.68/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_3265,plain,
% 19.68/3.00      ( sK7 = k1_xboole_0
% 19.68/3.00      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 19.68/3.00      | r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_2016,c_932]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_3,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 19.68/3.00      inference(cnf_transformation,[],[f55]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1333,plain,
% 19.68/3.00      ( ~ v1_relat_1(k2_zfmisc_1(sK6,sK7)) | v1_relat_1(sK9) ),
% 19.68/3.00      inference(resolution,[status(thm)],[c_3,c_33]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4,plain,
% 19.68/3.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 19.68/3.00      inference(cnf_transformation,[],[f56]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1361,plain,
% 19.68/3.00      ( v1_relat_1(sK9) ),
% 19.68/3.00      inference(forward_subsumption_resolution,[status(thm)],[c_1333,c_4]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1362,plain,
% 19.68/3.00      ( v1_relat_1(sK9) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_3887,plain,
% 19.68/3.00      ( r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top
% 19.68/3.00      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 19.68/3.00      | sK7 = k1_xboole_0 ),
% 19.68/3.00      inference(global_propositional_subsumption,[status(thm)],[c_3265,c_1362]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_3888,plain,
% 19.68/3.00      ( sK7 = k1_xboole_0
% 19.68/3.00      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 19.68/3.00      | r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_3887]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_21,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 19.68/3.00      inference(cnf_transformation,[],[f73]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_919,plain,
% 19.68/3.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 19.68/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1592,plain,
% 19.68/3.00      ( k7_relset_1(sK6,sK7,sK9,X0) = k9_relat_1(sK9,X0) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_907,c_919]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_32,negated_conjecture,
% 19.68/3.00      ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
% 19.68/3.00      inference(cnf_transformation,[],[f86]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_908,plain,
% 19.68/3.00      ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1878,plain,
% 19.68/3.00      ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) = iProver_top ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_1592,c_908]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_7,plain,
% 19.68/3.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 19.68/3.00      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 19.68/3.00      | ~ v1_relat_1(X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f58]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_933,plain,
% 19.68/3.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 19.68/3.00      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 19.68/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_18,plain,
% 19.68/3.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 19.68/3.00      | ~ v1_funct_1(X2)
% 19.68/3.00      | ~ v1_relat_1(X2)
% 19.68/3.00      | k1_funct_1(X2,X0) = X1 ),
% 19.68/3.00      inference(cnf_transformation,[],[f70]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_922,plain,
% 19.68/3.00      ( k1_funct_1(X0,X1) = X2
% 19.68/3.00      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 19.68/3.00      | v1_funct_1(X0) != iProver_top
% 19.68/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_3513,plain,
% 19.68/3.00      ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
% 19.68/3.00      | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
% 19.68/3.00      | v1_funct_1(X0) != iProver_top
% 19.68/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_933,c_922]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_10928,plain,
% 19.68/3.00      ( k1_funct_1(sK9,sK0(sK10,sK8,sK9)) = sK10
% 19.68/3.00      | v1_funct_1(sK9) != iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_1878,c_3513]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_35,negated_conjecture,
% 19.68/3.00      ( v1_funct_1(sK9) ),
% 19.68/3.00      inference(cnf_transformation,[],[f83]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_36,plain,
% 19.68/3.00      ( v1_funct_1(sK9) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_11472,plain,
% 19.68/3.00      ( k1_funct_1(sK9,sK0(sK10,sK8,sK9)) = sK10 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_10928,c_36,c_1362]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_31,negated_conjecture,
% 19.68/3.00      ( ~ r2_hidden(X0,sK6)
% 19.68/3.00      | ~ r2_hidden(X0,sK8)
% 19.68/3.00      | k1_funct_1(sK9,X0) != sK10 ),
% 19.68/3.00      inference(cnf_transformation,[],[f87]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_909,plain,
% 19.68/3.00      ( k1_funct_1(sK9,X0) != sK10
% 19.68/3.00      | r2_hidden(X0,sK6) != iProver_top
% 19.68/3.00      | r2_hidden(X0,sK8) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_11477,plain,
% 19.68/3.00      ( r2_hidden(sK0(sK10,sK8,sK9),sK6) != iProver_top
% 19.68/3.00      | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_11472,c_909]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_11726,plain,
% 19.68/3.00      ( sK7 = k1_xboole_0
% 19.68/3.00      | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top
% 19.68/3.00      | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_3888,c_11477]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_11744,plain,
% 19.68/3.00      ( r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top | sK7 = k1_xboole_0 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_11726,c_1878]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_11745,plain,
% 19.68/3.00      ( sK7 = k1_xboole_0 | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_11744]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_11750,plain,
% 19.68/3.00      ( sK7 = k1_xboole_0
% 19.68/3.00      | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_934,c_11745]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12039,plain,
% 19.68/3.00      ( sK7 = k1_xboole_0 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_11750,c_1362,c_1878]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12075,plain,
% 19.68/3.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_12039,c_907]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_26,plain,
% 19.68/3.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 19.68/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 19.68/3.00      | k1_xboole_0 = X1
% 19.68/3.00      | k1_xboole_0 = X0 ),
% 19.68/3.00      inference(cnf_transformation,[],[f96]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_914,plain,
% 19.68/3.00      ( k1_xboole_0 = X0
% 19.68/3.00      | k1_xboole_0 = X1
% 19.68/3.00      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 19.68/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12470,plain,
% 19.68/3.00      ( sK6 = k1_xboole_0
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | v1_funct_2(sK9,sK6,k1_xboole_0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_12075,c_914]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_37,plain,
% 19.68/3.00      ( v1_funct_2(sK9,sK6,sK7) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_331,plain,( X0 = X0 ),theory(equality) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_358,plain,
% 19.68/3.00      ( k1_xboole_0 = k1_xboole_0 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_331]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1564,plain,
% 19.68/3.00      ( sK9 = sK9 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_331]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_332,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1947,plain,
% 19.68/3.00      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_332]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1948,plain,
% 19.68/3.00      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1947]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_344,plain,
% 19.68/3.00      ( ~ v1_funct_2(X0,X1,X2)
% 19.68/3.00      | v1_funct_2(X3,X4,X5)
% 19.68/3.00      | X3 != X0
% 19.68/3.00      | X4 != X1
% 19.68/3.00      | X5 != X2 ),
% 19.68/3.00      theory(equality) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1422,plain,
% 19.68/3.00      ( v1_funct_2(X0,X1,X2)
% 19.68/3.00      | ~ v1_funct_2(sK9,sK6,sK7)
% 19.68/3.00      | X2 != sK7
% 19.68/3.00      | X1 != sK6
% 19.68/3.00      | X0 != sK9 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_344]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1563,plain,
% 19.68/3.00      ( v1_funct_2(sK9,X0,X1)
% 19.68/3.00      | ~ v1_funct_2(sK9,sK6,sK7)
% 19.68/3.00      | X1 != sK7
% 19.68/3.00      | X0 != sK6
% 19.68/3.00      | sK9 != sK9 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1422]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2473,plain,
% 19.68/3.00      ( v1_funct_2(sK9,sK6,X0)
% 19.68/3.00      | ~ v1_funct_2(sK9,sK6,sK7)
% 19.68/3.00      | X0 != sK7
% 19.68/3.00      | sK6 != sK6
% 19.68/3.00      | sK9 != sK9 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1563]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2475,plain,
% 19.68/3.00      ( X0 != sK7
% 19.68/3.00      | sK6 != sK6
% 19.68/3.00      | sK9 != sK9
% 19.68/3.00      | v1_funct_2(sK9,sK6,X0) = iProver_top
% 19.68/3.00      | v1_funct_2(sK9,sK6,sK7) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_2473]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2477,plain,
% 19.68/3.00      ( sK6 != sK6
% 19.68/3.00      | sK9 != sK9
% 19.68/3.00      | k1_xboole_0 != sK7
% 19.68/3.00      | v1_funct_2(sK9,sK6,sK7) != iProver_top
% 19.68/3.00      | v1_funct_2(sK9,sK6,k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_2475]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2474,plain,
% 19.68/3.00      ( sK6 = sK6 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_331]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12876,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_12470,c_37,c_358,c_1362,c_1564,c_1878,c_1948,c_2477,
% 19.68/3.00                 c_2474,c_11750]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12877,plain,
% 19.68/3.00      ( sK6 = k1_xboole_0 | sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_12876]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12881,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_12877,c_12075]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_338,plain,
% 19.68/3.00      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 19.68/3.00      theory(equality) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_350,plain,
% 19.68/3.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 19.68/3.00      | k1_xboole_0 != k1_xboole_0 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_338]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2,plain,
% 19.68/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1265,plain,
% 19.68/3.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 19.68/3.00      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_2]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1266,plain,
% 19.68/3.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
% 19.68/3.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1268,plain,
% 19.68/3.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 19.68/3.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1266]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_0,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,X0) ),
% 19.68/3.00      inference(cnf_transformation,[],[f52]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1518,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1519,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1521,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1519]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_336,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.68/3.00      theory(equality) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1346,plain,
% 19.68/3.00      ( m1_subset_1(X0,X1)
% 19.68/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 19.68/3.00      | X0 != X2
% 19.68/3.00      | X1 != k1_zfmisc_1(X3) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_336]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2194,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.68/3.00      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.68/3.00      | X2 != X0
% 19.68/3.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1346]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4186,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 19.68/3.00      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 19.68/3.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 19.68/3.00      | sK9 != X0 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_2194]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4187,plain,
% 19.68/3.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 19.68/3.00      | sK9 != X0
% 19.68/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 19.68/3.00      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_4186]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4189,plain,
% 19.68/3.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 19.68/3.00      | sK9 != k1_xboole_0
% 19.68/3.00      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 19.68/3.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_4187]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_335,plain,
% 19.68/3.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 19.68/3.00      theory(equality) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_9524,plain,
% 19.68/3.00      ( k2_zfmisc_1(X0,k1_xboole_0) != k2_zfmisc_1(X0,k1_xboole_0)
% 19.68/3.00      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_335]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_9525,plain,
% 19.68/3.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 19.68/3.00      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_9524]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_13542,plain,
% 19.68/3.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_12881,c_350,c_358,c_1268,c_1521,c_4189,c_9525]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_13552,plain,
% 19.68/3.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK9) = k1_relat_1(sK9) ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_13542,c_920]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_29,plain,
% 19.68/3.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 19.68/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 19.68/3.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 19.68/3.00      inference(cnf_transformation,[],[f98]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_911,plain,
% 19.68/3.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 19.68/3.00      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 19.68/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_13554,plain,
% 19.68/3.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK9) = k1_xboole_0
% 19.68/3.00      | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_13542,c_911]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_13560,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = k1_xboole_0
% 19.68/3.00      | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_13552,c_13554]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2325,plain,
% 19.68/3.00      ( ~ v1_funct_2(X0,X1,X2)
% 19.68/3.00      | v1_funct_2(sK9,X3,k1_xboole_0)
% 19.68/3.00      | X3 != X1
% 19.68/3.00      | sK9 != X0
% 19.68/3.00      | k1_xboole_0 != X2 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_344]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2326,plain,
% 19.68/3.00      ( X0 != X1
% 19.68/3.00      | sK9 != X2
% 19.68/3.00      | k1_xboole_0 != X3
% 19.68/3.00      | v1_funct_2(X2,X1,X3) != iProver_top
% 19.68/3.00      | v1_funct_2(sK9,X0,k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_2325]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2328,plain,
% 19.68/3.00      ( sK9 != k1_xboole_0
% 19.68/3.00      | k1_xboole_0 != k1_xboole_0
% 19.68/3.00      | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) = iProver_top
% 19.68/3.00      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_2326]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_15,plain,
% 19.68/3.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 19.68/3.00      | r2_hidden(sK3(X1,X2,X0),X2)
% 19.68/3.00      | ~ v1_funct_1(X1)
% 19.68/3.00      | ~ v1_relat_1(X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f91]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2427,plain,
% 19.68/3.00      ( r2_hidden(sK3(sK9,X0,sK10),X0)
% 19.68/3.00      | ~ r2_hidden(sK10,k9_relat_1(sK9,X0))
% 19.68/3.00      | ~ v1_funct_1(sK9)
% 19.68/3.00      | ~ v1_relat_1(sK9) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_15]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_24422,plain,
% 19.68/3.00      ( r2_hidden(sK3(sK9,sK8,sK10),sK8)
% 19.68/3.00      | ~ r2_hidden(sK10,k9_relat_1(sK9,sK8))
% 19.68/3.00      | ~ v1_funct_1(sK9)
% 19.68/3.00      | ~ v1_relat_1(sK9) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_2427]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_24425,plain,
% 19.68/3.00      ( r2_hidden(sK3(sK9,sK8,sK10),sK8) = iProver_top
% 19.68/3.00      | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
% 19.68/3.00      | v1_funct_1(sK9) != iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_24422]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_905,plain,
% 19.68/3.00      ( v1_funct_1(sK9) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_940,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_24,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.00      | r2_hidden(sK5(X1,X0),X1)
% 19.68/3.00      | k1_relset_1(X1,X2,X0) = X1 ),
% 19.68/3.00      inference(cnf_transformation,[],[f74]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_916,plain,
% 19.68/3.00      ( k1_relset_1(X0,X1,X2) = X0
% 19.68/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.00      | r2_hidden(sK5(X0,X2),X0) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2584,plain,
% 19.68/3.00      ( k1_relset_1(sK6,sK7,sK9) = sK6
% 19.68/3.00      | r2_hidden(sK5(sK6,sK9),sK6) = iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_907,c_916]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2587,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6 | r2_hidden(sK5(sK6,sK9),sK6) = iProver_top ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_2584,c_1474]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_938,plain,
% 19.68/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 19.68/3.00      | r1_tarski(X0,X1) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.68/3.00      | ~ r2_hidden(X2,X0)
% 19.68/3.00      | r2_hidden(X2,X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_939,plain,
% 19.68/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.68/3.00      | r2_hidden(X2,X0) != iProver_top
% 19.68/3.00      | r2_hidden(X2,X1) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2344,plain,
% 19.68/3.00      ( r2_hidden(X0,X1) != iProver_top
% 19.68/3.00      | r2_hidden(X0,X2) = iProver_top
% 19.68/3.00      | r1_tarski(X1,X2) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_938,c_939]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_3045,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | r2_hidden(sK5(sK6,sK9),X0) = iProver_top
% 19.68/3.00      | r1_tarski(sK6,X0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_2587,c_2344]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_3864,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | r2_hidden(sK5(sK6,sK9),X0) = iProver_top
% 19.68/3.00      | r1_tarski(X1,X0) != iProver_top
% 19.68/3.00      | r1_tarski(sK6,X1) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_3045,c_2344]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4311,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | r2_hidden(sK5(sK6,sK9),X0) = iProver_top
% 19.68/3.00      | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_940,c_3864]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_14,plain,
% 19.68/3.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 19.68/3.00      | ~ v1_funct_1(X1)
% 19.68/3.00      | ~ v1_relat_1(X1)
% 19.68/3.00      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 19.68/3.00      inference(cnf_transformation,[],[f90]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_926,plain,
% 19.68/3.00      ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
% 19.68/3.00      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 19.68/3.00      | v1_funct_1(X0) != iProver_top
% 19.68/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_7859,plain,
% 19.68/3.00      ( k1_funct_1(X0,sK3(X0,X1,sK5(sK6,sK9))) = sK5(sK6,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | r1_tarski(sK6,k1_xboole_0) != iProver_top
% 19.68/3.00      | v1_funct_1(X0) != iProver_top
% 19.68/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_4311,c_926]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_24697,plain,
% 19.68/3.00      ( k1_funct_1(X0,sK3(X0,X1,sK5(sK6,sK9))) = sK5(sK6,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 19.68/3.00      | v1_funct_1(X0) != iProver_top
% 19.68/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_12877,c_7859]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_129,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_131,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_129]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_24793,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | k1_funct_1(X0,sK3(X0,X1,sK5(sK6,sK9))) = sK5(sK6,sK9)
% 19.68/3.00      | v1_funct_1(X0) != iProver_top
% 19.68/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.00      inference(global_propositional_subsumption,[status(thm)],[c_24697,c_131]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_24794,plain,
% 19.68/3.00      ( k1_funct_1(X0,sK3(X0,X1,sK5(sK6,sK9))) = sK5(sK6,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | v1_funct_1(X0) != iProver_top
% 19.68/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_24793]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_24804,plain,
% 19.68/3.00      ( k1_funct_1(sK9,sK3(sK9,X0,sK5(sK6,sK9))) = sK5(sK6,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_905,c_24794]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_24805,plain,
% 19.68/3.00      ( ~ v1_relat_1(sK9)
% 19.68/3.00      | k1_funct_1(sK9,sK3(sK9,X0,sK5(sK6,sK9))) = sK5(sK6,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_24804]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_25013,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | k1_funct_1(sK9,sK3(sK9,X0,sK5(sK6,sK9))) = sK5(sK6,sK9) ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_24804,c_1362]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_25014,plain,
% 19.68/3.00      ( k1_funct_1(sK9,sK3(sK9,X0,sK5(sK6,sK9))) = sK5(sK6,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_25013]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_25019,plain,
% 19.68/3.00      ( k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(sK6,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_12877,c_25014]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12884,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,sK9),X0) = iProver_top
% 19.68/3.00      | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_12877,c_4311]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12887,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,sK9),k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_12877,c_2587]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_17263,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,sK9),X0) = iProver_top
% 19.68/3.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_12887,c_2344]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_17427,plain,
% 19.68/3.00      ( r2_hidden(sK5(k1_xboole_0,sK9),X0) = iProver_top
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | k1_relat_1(sK9) = sK6 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_12884,c_129,c_17263]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_17428,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,sK9),X0) = iProver_top ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_17427]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_17435,plain,
% 19.68/3.00      ( k1_funct_1(X0,sK3(X0,X1,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | v1_funct_1(X0) != iProver_top
% 19.68/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_17428,c_926]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_20031,plain,
% 19.68/3.00      ( k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_905,c_17435]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_20032,plain,
% 19.68/3.00      ( ~ v1_relat_1(sK9)
% 19.68/3.00      | k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_20031]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_20113,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9) ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_20031,c_1361,c_20032]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_20114,plain,
% 19.68/3.00      ( k1_funct_1(sK9,sK3(sK9,X0,sK5(k1_xboole_0,sK9))) = sK5(k1_xboole_0,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_20113]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_25212,plain,
% 19.68/3.00      ( sK5(k1_xboole_0,sK9) = sK5(sK6,sK9)
% 19.68/3.00      | k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_25019,c_20114]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_17,plain,
% 19.68/3.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.68/3.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 19.68/3.00      | ~ v1_funct_1(X1)
% 19.68/3.00      | ~ v1_relat_1(X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f93]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_923,plain,
% 19.68/3.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 19.68/3.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 19.68/3.00      | v1_funct_1(X1) != iProver_top
% 19.68/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_23,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.00      | ~ r2_hidden(k4_tarski(sK5(X1,X0),X3),X0)
% 19.68/3.00      | k1_relset_1(X1,X2,X0) = X1 ),
% 19.68/3.00      inference(cnf_transformation,[],[f75]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_917,plain,
% 19.68/3.00      ( k1_relset_1(X0,X1,X2) = X0
% 19.68/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.00      | r2_hidden(k4_tarski(sK5(X0,X2),X3),X2) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4493,plain,
% 19.68/3.00      ( k1_relset_1(X0,X1,X2) = X0
% 19.68/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.68/3.00      | r2_hidden(sK5(X0,X2),k1_relat_1(X2)) != iProver_top
% 19.68/3.00      | v1_funct_1(X2) != iProver_top
% 19.68/3.00      | v1_relat_1(X2) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_923,c_917]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_28719,plain,
% 19.68/3.00      ( k1_relset_1(sK6,k1_xboole_0,sK9) = sK6
% 19.68/3.00      | r2_hidden(sK5(sK6,sK9),k1_relat_1(sK9)) != iProver_top
% 19.68/3.00      | v1_funct_1(sK9) != iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_12075,c_4493]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12074,plain,
% 19.68/3.00      ( k1_relset_1(sK6,k1_xboole_0,sK9) = k1_relat_1(sK9) ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_12039,c_1474]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_28724,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | r2_hidden(sK5(sK6,sK9),k1_relat_1(sK9)) != iProver_top
% 19.68/3.00      | v1_funct_1(sK9) != iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_28719,c_12074]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_29120,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | r2_hidden(sK5(sK6,sK9),k1_relat_1(sK9)) != iProver_top ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_28724,c_36,c_1362]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_29128,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6
% 19.68/3.00      | sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,sK9),k1_relat_1(sK9)) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_25212,c_29120]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_29405,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = sK6 | sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(forward_subsumption_resolution,[status(thm)],[c_29128,c_17428]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_16,plain,
% 19.68/3.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 19.68/3.00      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 19.68/3.00      | ~ v1_funct_1(X1)
% 19.68/3.00      | ~ v1_relat_1(X1) ),
% 19.68/3.00      inference(cnf_transformation,[],[f92]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_924,plain,
% 19.68/3.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 19.68/3.00      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 19.68/3.00      | v1_funct_1(X1) != iProver_top
% 19.68/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_29406,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 19.68/3.00      | r2_hidden(sK3(sK9,X1,X0),sK6) = iProver_top
% 19.68/3.00      | v1_funct_1(sK9) != iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_29405,c_924]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_31089,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 19.68/3.00      | r2_hidden(sK3(sK9,X1,X0),sK6) = iProver_top ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_29406,c_36,c_1362]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4792,plain,
% 19.68/3.00      ( k1_funct_1(sK9,sK3(sK9,sK8,sK10)) = sK10
% 19.68/3.00      | v1_funct_1(sK9) != iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_1878,c_926]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5118,plain,
% 19.68/3.00      ( k1_funct_1(sK9,sK3(sK9,sK8,sK10)) = sK10 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_4792,c_36,c_1362]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5122,plain,
% 19.68/3.00      ( r2_hidden(sK3(sK9,sK8,sK10),sK6) != iProver_top
% 19.68/3.00      | r2_hidden(sK3(sK9,sK8,sK10),sK8) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_5118,c_909]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_31100,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(sK3(sK9,sK8,sK10),sK8) != iProver_top
% 19.68/3.00      | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_31089,c_5122]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_29407,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 19.68/3.00      | r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_29405,c_932]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_30786,plain,
% 19.68/3.00      ( r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top
% 19.68/3.00      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 19.68/3.00      | sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_29407,c_1362]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_30787,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 19.68/3.00      | r2_hidden(sK0(X0,X1,sK9),sK6) = iProver_top ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_30786]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_30798,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0
% 19.68/3.00      | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top
% 19.68/3.00      | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_30787,c_11477]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_31532,plain,
% 19.68/3.00      ( sK9 = k1_xboole_0 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_30798,c_36,c_1362,c_1878,c_24425,c_31100]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_27,plain,
% 19.68/3.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 19.68/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 19.68/3.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 19.68/3.00      inference(cnf_transformation,[],[f97]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_913,plain,
% 19.68/3.00      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 19.68/3.00      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 19.68/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_13586,plain,
% 19.68/3.00      ( k1_relat_1(sK9) != k1_xboole_0
% 19.68/3.00      | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) = iProver_top
% 19.68/3.00      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_13552,c_913]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_14420,plain,
% 19.68/3.00      ( v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) = iProver_top
% 19.68/3.00      | k1_relat_1(sK9) != k1_xboole_0 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_13586,c_350,c_358,c_1268,c_1521,c_4189,c_9525,c_12881]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_14421,plain,
% 19.68/3.00      ( k1_relat_1(sK9) != k1_xboole_0
% 19.68/3.00      | v1_funct_2(sK9,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_14420]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_31597,plain,
% 19.68/3.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 19.68/3.00      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_31532,c_14421]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_52,plain,
% 19.68/3.00      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 19.68/3.00      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 19.68/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_54,plain,
% 19.68/3.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.68/3.00      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 19.68/3.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_52]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_121,plain,
% 19.68/3.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_123,plain,
% 19.68/3.00      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_121]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1270,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.68/3.00      | v1_relat_1(X0)
% 19.68/3.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_3]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1271,plain,
% 19.68/3.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.68/3.00      | v1_relat_1(X0) = iProver_top
% 19.68/3.00      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1273,plain,
% 19.68/3.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 19.68/3.00      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 19.68/3.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1271]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_341,plain,
% 19.68/3.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 19.68/3.00      theory(equality) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1300,plain,
% 19.68/3.00      ( v1_funct_1(X0) | ~ v1_funct_1(sK9) | X0 != sK9 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_341]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1301,plain,
% 19.68/3.00      ( X0 != sK9
% 19.68/3.00      | v1_funct_1(X0) = iProver_top
% 19.68/3.00      | v1_funct_1(sK9) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_1300]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1303,plain,
% 19.68/3.00      ( k1_xboole_0 != sK9
% 19.68/3.00      | v1_funct_1(sK9) != iProver_top
% 19.68/3.00      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1301]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1516,plain,
% 19.68/3.00      ( X0 != X1 | X0 = sK9 | sK9 != X1 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_332]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_1517,plain,
% 19.68/3.00      ( sK9 != k1_xboole_0 | k1_xboole_0 = sK9 | k1_xboole_0 != k1_xboole_0 ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1516]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4565,plain,
% 19.68/3.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 19.68/3.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top
% 19.68/3.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 19.68/3.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_4493]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4665,plain,
% 19.68/3.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 19.68/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,X0),k1_xboole_0) ),
% 19.68/3.00      inference(resolution,[status(thm)],[c_27,c_24]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4666,plain,
% 19.68/3.00      ( v1_funct_2(X0,k1_xboole_0,X1) = iProver_top
% 19.68/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_4665]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_4668,plain,
% 19.68/3.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 19.68/3.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_4666]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_2706,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.68/3.00      | ~ r2_hidden(sK5(X0,X2),X0)
% 19.68/3.00      | r2_hidden(sK5(X0,X2),X1) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_1]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5173,plain,
% 19.68/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1)))
% 19.68/3.00      | ~ r2_hidden(sK5(X0,X2),X0)
% 19.68/3.00      | r2_hidden(sK5(X0,X2),k1_relat_1(X1)) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_2706]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5175,plain,
% 19.68/3.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1))) != iProver_top
% 19.68/3.00      | r2_hidden(sK5(X0,X2),X0) != iProver_top
% 19.68/3.00      | r2_hidden(sK5(X0,X2),k1_relat_1(X1)) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_5173]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_5177,plain,
% 19.68/3.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) != iProver_top
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
% 19.68/3.00      | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_5175]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_9321,plain,
% 19.68/3.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1)))
% 19.68/3.00      | ~ r1_tarski(X0,k1_relat_1(X1)) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_2]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_9322,plain,
% 19.68/3.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1))) = iProver_top
% 19.68/3.00      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_9321]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_9324,plain,
% 19.68/3.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) = iProver_top
% 19.68/3.00      | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_9322]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_21034,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_0]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_21037,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top ),
% 19.68/3.00      inference(predicate_to_equality,[status(thm)],[c_21034]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_21039,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top ),
% 19.68/3.00      inference(instantiation,[status(thm)],[c_21037]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_36671,plain,
% 19.68/3.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_31597,c_36,c_54,c_123,c_358,c_1268,c_1273,c_1303,c_1362,
% 19.68/3.00                 c_1517,c_1521,c_1878,c_4565,c_4668,c_5177,c_9324,c_21039,
% 19.68/3.00                 c_24425,c_31100]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_72441,plain,
% 19.68/3.00      ( k1_relat_1(sK9) = k1_xboole_0 ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_13560,c_36,c_54,c_123,c_358,c_1268,c_1273,c_1303,c_1362,
% 19.68/3.00                 c_1517,c_1521,c_1878,c_2328,c_4565,c_4668,c_5177,c_9324,
% 19.68/3.00                 c_21039,c_24425,c_31100]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_72443,plain,
% 19.68/3.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.68/3.00      inference(light_normalisation,[status(thm)],[c_72441,c_31532]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_3266,plain,
% 19.68/3.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 19.68/3.00      | r2_hidden(sK0(X0,X2,X1),X3) = iProver_top
% 19.68/3.00      | r1_tarski(k1_relat_1(X1),X3) != iProver_top
% 19.68/3.00      | v1_relat_1(X1) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_932,c_2344]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_12586,plain,
% 19.68/3.00      ( r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top
% 19.68/3.00      | r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
% 19.68/3.00      | r1_tarski(k1_relat_1(sK9),sK6) != iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_3266,c_11477]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_13393,plain,
% 19.68/3.00      ( r1_tarski(k1_relat_1(sK9),sK6) != iProver_top
% 19.68/3.00      | r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_12586,c_1362,c_1878]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_13394,plain,
% 19.68/3.00      ( r2_hidden(sK0(sK10,sK8,sK9),sK8) != iProver_top
% 19.68/3.00      | r1_tarski(k1_relat_1(sK9),sK6) != iProver_top ),
% 19.68/3.00      inference(renaming,[status(thm)],[c_13393]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_13399,plain,
% 19.68/3.00      ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top
% 19.68/3.00      | r1_tarski(k1_relat_1(sK9),sK6) != iProver_top
% 19.68/3.00      | v1_relat_1(sK9) != iProver_top ),
% 19.68/3.00      inference(superposition,[status(thm)],[c_934,c_13394]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_14131,plain,
% 19.68/3.00      ( r1_tarski(k1_relat_1(sK9),sK6) != iProver_top ),
% 19.68/3.00      inference(global_propositional_subsumption,
% 19.68/3.00                [status(thm)],
% 19.68/3.00                [c_13399,c_1362,c_1878]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_31598,plain,
% 19.68/3.00      ( r1_tarski(k1_relat_1(k1_xboole_0),sK6) != iProver_top ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_31532,c_14131]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_72483,plain,
% 19.68/3.00      ( r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 19.68/3.00      inference(demodulation,[status(thm)],[c_72443,c_31598]) ).
% 19.68/3.00  
% 19.68/3.00  cnf(c_74962,plain,
% 19.68/3.00      ( $false ),
% 19.68/3.00      inference(forward_subsumption_resolution,[status(thm)],[c_72483,c_940]) ).
% 19.68/3.00  
% 19.68/3.00  
% 19.68/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.68/3.00  
% 19.68/3.00  ------                               Statistics
% 19.68/3.00  
% 19.68/3.00  ------ Selected
% 19.68/3.00  
% 19.68/3.00  total_time:                             2.161
% 19.68/3.00  
%------------------------------------------------------------------------------

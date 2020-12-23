%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:47 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  217 (2694 expanded)
%              Number of clauses        :  150 ( 921 expanded)
%              Number of leaves         :   20 ( 611 expanded)
%              Depth                    :   29
%              Number of atoms          :  680 (13306 expanded)
%              Number of equality atoms :  335 (2631 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f28])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK9
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)) ) ) ),
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
              ( k1_funct_1(sK8,X5) != X4
              | ~ r2_hidden(X5,sK7)
              | ~ r2_hidden(X5,sK5) )
          & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7)) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ r2_hidden(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f29,f50,f49])).

fof(f86,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ r2_hidden(X5,sK5) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f97,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_610,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_611,plain,
    ( v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_924,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_611])).

cnf(c_925,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK4(X0,X1,sK8),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_924])).

cnf(c_1371,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK4(X0,X1,sK8),X1)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_925])).

cnf(c_1922,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK8),X1) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_1372,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_925])).

cnf(c_1417,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1372])).

cnf(c_1418,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK8),X1) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_1384,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2209,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_939,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_611])).

cnf(c_940,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X2),sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_22,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_381,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_382,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_804,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(resolution,[status(thm)],[c_611,c_382])).

cnf(c_947,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK8,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_940,c_804])).

cnf(c_1368,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_947])).

cnf(c_2210,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_2213,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2210])).

cnf(c_2738,plain,
    ( r2_hidden(sK4(X0,X1,sK8),X1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1922,c_1417,c_1418,c_2209,c_2213])).

cnf(c_2739,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK8),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2738])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_556,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_34])).

cnf(c_557,plain,
    ( ~ v1_funct_2(sK8,X0,X1)
    | k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_1084,plain,
    ( k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK6 != X1
    | sK5 != X0
    | sK8 != sK8
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_557])).

cnf(c_1085,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_1084])).

cnf(c_1160,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_xboole_0 = sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_1085])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_601,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_602,plain,
    ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_2200,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(equality_resolution,[status(thm)],[c_602])).

cnf(c_2270,plain,
    ( k1_relat_1(sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1160,c_2200])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_894,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_611])).

cnf(c_895,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_1375,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8))
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_895])).

cnf(c_1928,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8)) = iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_1376,plain,
    ( sP4_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_895])).

cnf(c_1427,plain,
    ( sP4_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1376])).

cnf(c_1428,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8)) = iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_2850,plain,
    ( r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1928,c_1427,c_1428,c_2209,c_2213])).

cnf(c_2851,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2850])).

cnf(c_2858,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2270,c_2851])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_592,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_593,plain,
    ( k7_relset_1(X0,X1,sK8,X2) = k9_relat_1(sK8,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_2203,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(equality_resolution,[status(thm)],[c_593])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1942,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2217,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2203,c_1942])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_909,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_611])).

cnf(c_910,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_909])).

cnf(c_1373,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_910])).

cnf(c_1925,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8) = iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1373])).

cnf(c_1374,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_910])).

cnf(c_1422,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1374])).

cnf(c_1423,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8) = iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1373])).

cnf(c_2878,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1925,c_1422,c_1423,c_2209,c_2213])).

cnf(c_2879,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_2878])).

cnf(c_21,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_411,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_412,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_776,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | k1_funct_1(sK8,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(resolution,[status(thm)],[c_611,c_412])).

cnf(c_1381,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | k1_funct_1(sK8,X0) = X1
    | ~ sP7_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP7_iProver_split])],[c_776])).

cnf(c_1939,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | sP7_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_1382,plain,
    ( sP7_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_776])).

cnf(c_1444,plain,
    ( sP7_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_1445,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | sP7_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_2540,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | k1_funct_1(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1939,c_1444,c_1445,c_2209,c_2213])).

cnf(c_2541,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_2540])).

cnf(c_2888,plain,
    ( k1_funct_1(sK8,sK4(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2879,c_2541])).

cnf(c_4958,plain,
    ( k1_funct_1(sK8,sK4(sK9,sK7,sK8)) = sK9 ),
    inference(superposition,[status(thm)],[c_2217,c_2888])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1943,plain,
    ( k1_funct_1(sK8,X0) != sK9
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5002,plain,
    ( r2_hidden(sK4(sK9,sK7,sK8),sK5) != iProver_top
    | r2_hidden(sK4(sK9,sK7,sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_1943])).

cnf(c_6090,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK9,sK7,sK8),sK7) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2858,c_5002])).

cnf(c_6885,plain,
    ( r2_hidden(sK4(sK9,sK7,sK8),sK7) != iProver_top
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6090,c_2217])).

cnf(c_6886,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK9,sK7,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_6885])).

cnf(c_6891,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_6886])).

cnf(c_6894,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6891,c_2217])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2275,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_602])).

cnf(c_6904,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6894,c_2275])).

cnf(c_6933,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6904,c_9])).

cnf(c_6934,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK8) = k1_relat_1(sK8) ),
    inference(equality_resolution_simp,[status(thm)],[c_6933])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_657,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_658,plain,
    ( ~ v1_funct_2(sK8,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_1109,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK6 != X0
    | sK5 != k1_xboole_0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_658])).

cnf(c_1110,plain,
    ( k1_relset_1(k1_xboole_0,sK6,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK5 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1109])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2072,plain,
    ( k1_relset_1(k1_xboole_0,sK6,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1110,c_10])).

cnf(c_6905,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6894,c_2072])).

cnf(c_6927,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6905,c_9])).

cnf(c_6928,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6927])).

cnf(c_6935,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6934,c_6928])).

cnf(c_1386,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5487,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK8))
    | k1_relat_1(sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_5489,plain,
    ( v1_xboole_0(k1_relat_1(sK8))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK8) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5487])).

cnf(c_1390,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2239,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK5,sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_5283,plain,
    ( k2_zfmisc_1(sK5,k1_xboole_0) != k2_zfmisc_1(sK5,sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1952,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3217,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2851,c_1952])).

cnf(c_4528,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_3217])).

cnf(c_4533,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4528])).

cnf(c_15,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_833,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
    | ~ v1_xboole_0(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_834,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_833])).

cnf(c_844,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_834,c_1])).

cnf(c_3507,plain,
    ( ~ r2_hidden(sK0(k9_relat_1(sK8,sK7)),k9_relat_1(sK8,sK7))
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_1389,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2350,plain,
    ( X0 != sK6
    | X1 != sK5
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_2614,plain,
    ( X0 != sK5
    | k2_zfmisc_1(X0,k1_xboole_0) = k2_zfmisc_1(sK5,sK6)
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2350])).

cnf(c_2942,plain,
    ( k2_zfmisc_1(sK5,k1_xboole_0) = k2_zfmisc_1(sK5,sK6)
    | sK5 != sK5
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2614])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2781,plain,
    ( r2_hidden(sK0(k9_relat_1(sK8,sK7)),k9_relat_1(sK8,sK7))
    | v1_xboole_0(k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1385,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2621,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_2622,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_2211,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_2502,plain,
    ( k7_relset_1(sK5,sK6,sK8,sK7) = k9_relat_1(sK8,sK7)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_2300,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7))
    | k7_relset_1(sK5,sK6,sK8,sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_2501,plain,
    ( v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7))
    | ~ v1_xboole_0(k9_relat_1(sK8,sK7))
    | k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_2345,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_2259,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_2344,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_2234,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_2236,plain,
    ( v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2234])).

cnf(c_2225,plain,
    ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | ~ v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_639,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_640,plain,
    ( ~ v1_funct_2(sK8,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK8 ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_1095,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK6 != k1_xboole_0
    | sK5 != X0
    | sK8 != sK8
    | sK8 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_640])).

cnf(c_1096,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK6 != k1_xboole_0
    | sK8 = k1_xboole_0
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_1095])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_102,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6935,c_6891,c_5489,c_5283,c_4533,c_3507,c_2942,c_2781,c_2622,c_2502,c_2501,c_2345,c_2344,c_2236,c_2225,c_2217,c_2209,c_1096,c_2,c_103,c_102,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.35/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/0.98  
% 3.35/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/0.98  
% 3.35/0.98  ------  iProver source info
% 3.35/0.98  
% 3.35/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.35/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/0.98  git: non_committed_changes: false
% 3.35/0.98  git: last_make_outside_of_git: false
% 3.35/0.98  
% 3.35/0.98  ------ 
% 3.35/0.98  
% 3.35/0.98  ------ Input Options
% 3.35/0.98  
% 3.35/0.98  --out_options                           all
% 3.35/0.98  --tptp_safe_out                         true
% 3.35/0.98  --problem_path                          ""
% 3.35/0.98  --include_path                          ""
% 3.35/0.98  --clausifier                            res/vclausify_rel
% 3.35/0.98  --clausifier_options                    --mode clausify
% 3.35/0.98  --stdin                                 false
% 3.35/0.98  --stats_out                             all
% 3.35/0.98  
% 3.35/0.98  ------ General Options
% 3.35/0.98  
% 3.35/0.98  --fof                                   false
% 3.35/0.98  --time_out_real                         305.
% 3.35/0.98  --time_out_virtual                      -1.
% 3.35/0.98  --symbol_type_check                     false
% 3.35/0.98  --clausify_out                          false
% 3.35/0.98  --sig_cnt_out                           false
% 3.35/0.98  --trig_cnt_out                          false
% 3.35/0.98  --trig_cnt_out_tolerance                1.
% 3.35/0.98  --trig_cnt_out_sk_spl                   false
% 3.35/0.98  --abstr_cl_out                          false
% 3.35/0.98  
% 3.35/0.98  ------ Global Options
% 3.35/0.98  
% 3.35/0.98  --schedule                              default
% 3.35/0.98  --add_important_lit                     false
% 3.35/0.98  --prop_solver_per_cl                    1000
% 3.35/0.98  --min_unsat_core                        false
% 3.35/0.98  --soft_assumptions                      false
% 3.35/0.98  --soft_lemma_size                       3
% 3.35/0.98  --prop_impl_unit_size                   0
% 3.35/0.98  --prop_impl_unit                        []
% 3.35/0.98  --share_sel_clauses                     true
% 3.35/0.98  --reset_solvers                         false
% 3.35/0.98  --bc_imp_inh                            [conj_cone]
% 3.35/0.98  --conj_cone_tolerance                   3.
% 3.35/0.98  --extra_neg_conj                        none
% 3.35/0.98  --large_theory_mode                     true
% 3.35/0.98  --prolific_symb_bound                   200
% 3.35/0.98  --lt_threshold                          2000
% 3.35/0.98  --clause_weak_htbl                      true
% 3.35/0.98  --gc_record_bc_elim                     false
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing Options
% 3.35/0.98  
% 3.35/0.98  --preprocessing_flag                    true
% 3.35/0.98  --time_out_prep_mult                    0.1
% 3.35/0.98  --splitting_mode                        input
% 3.35/0.98  --splitting_grd                         true
% 3.35/0.98  --splitting_cvd                         false
% 3.35/0.98  --splitting_cvd_svl                     false
% 3.35/0.98  --splitting_nvd                         32
% 3.35/0.98  --sub_typing                            true
% 3.35/0.98  --prep_gs_sim                           true
% 3.35/0.98  --prep_unflatten                        true
% 3.35/0.98  --prep_res_sim                          true
% 3.35/0.98  --prep_upred                            true
% 3.35/0.98  --prep_sem_filter                       exhaustive
% 3.35/0.98  --prep_sem_filter_out                   false
% 3.35/0.98  --pred_elim                             true
% 3.35/0.98  --res_sim_input                         true
% 3.35/0.98  --eq_ax_congr_red                       true
% 3.35/0.98  --pure_diseq_elim                       true
% 3.35/0.98  --brand_transform                       false
% 3.35/0.98  --non_eq_to_eq                          false
% 3.35/0.98  --prep_def_merge                        true
% 3.35/0.98  --prep_def_merge_prop_impl              false
% 3.35/0.98  --prep_def_merge_mbd                    true
% 3.35/0.98  --prep_def_merge_tr_red                 false
% 3.35/0.98  --prep_def_merge_tr_cl                  false
% 3.35/0.98  --smt_preprocessing                     true
% 3.35/0.98  --smt_ac_axioms                         fast
% 3.35/0.98  --preprocessed_out                      false
% 3.35/0.98  --preprocessed_stats                    false
% 3.35/0.98  
% 3.35/0.98  ------ Abstraction refinement Options
% 3.35/0.98  
% 3.35/0.98  --abstr_ref                             []
% 3.35/0.98  --abstr_ref_prep                        false
% 3.35/0.98  --abstr_ref_until_sat                   false
% 3.35/0.98  --abstr_ref_sig_restrict                funpre
% 3.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.98  --abstr_ref_under                       []
% 3.35/0.98  
% 3.35/0.98  ------ SAT Options
% 3.35/0.98  
% 3.35/0.98  --sat_mode                              false
% 3.35/0.98  --sat_fm_restart_options                ""
% 3.35/0.98  --sat_gr_def                            false
% 3.35/0.98  --sat_epr_types                         true
% 3.35/0.98  --sat_non_cyclic_types                  false
% 3.35/0.98  --sat_finite_models                     false
% 3.35/0.98  --sat_fm_lemmas                         false
% 3.35/0.98  --sat_fm_prep                           false
% 3.35/0.98  --sat_fm_uc_incr                        true
% 3.35/0.98  --sat_out_model                         small
% 3.35/0.98  --sat_out_clauses                       false
% 3.35/0.98  
% 3.35/0.98  ------ QBF Options
% 3.35/0.98  
% 3.35/0.98  --qbf_mode                              false
% 3.35/0.98  --qbf_elim_univ                         false
% 3.35/0.98  --qbf_dom_inst                          none
% 3.35/0.98  --qbf_dom_pre_inst                      false
% 3.35/0.98  --qbf_sk_in                             false
% 3.35/0.98  --qbf_pred_elim                         true
% 3.35/0.98  --qbf_split                             512
% 3.35/0.98  
% 3.35/0.98  ------ BMC1 Options
% 3.35/0.98  
% 3.35/0.98  --bmc1_incremental                      false
% 3.35/0.98  --bmc1_axioms                           reachable_all
% 3.35/0.98  --bmc1_min_bound                        0
% 3.35/0.98  --bmc1_max_bound                        -1
% 3.35/0.98  --bmc1_max_bound_default                -1
% 3.35/0.98  --bmc1_symbol_reachability              true
% 3.35/0.98  --bmc1_property_lemmas                  false
% 3.35/0.98  --bmc1_k_induction                      false
% 3.35/0.98  --bmc1_non_equiv_states                 false
% 3.35/0.98  --bmc1_deadlock                         false
% 3.35/0.98  --bmc1_ucm                              false
% 3.35/0.98  --bmc1_add_unsat_core                   none
% 3.35/0.98  --bmc1_unsat_core_children              false
% 3.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.98  --bmc1_out_stat                         full
% 3.35/0.98  --bmc1_ground_init                      false
% 3.35/0.98  --bmc1_pre_inst_next_state              false
% 3.35/0.98  --bmc1_pre_inst_state                   false
% 3.35/0.98  --bmc1_pre_inst_reach_state             false
% 3.35/0.98  --bmc1_out_unsat_core                   false
% 3.35/0.98  --bmc1_aig_witness_out                  false
% 3.35/0.98  --bmc1_verbose                          false
% 3.35/0.98  --bmc1_dump_clauses_tptp                false
% 3.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.98  --bmc1_dump_file                        -
% 3.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.98  --bmc1_ucm_extend_mode                  1
% 3.35/0.98  --bmc1_ucm_init_mode                    2
% 3.35/0.98  --bmc1_ucm_cone_mode                    none
% 3.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.98  --bmc1_ucm_relax_model                  4
% 3.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.98  --bmc1_ucm_layered_model                none
% 3.35/0.98  --bmc1_ucm_max_lemma_size               10
% 3.35/0.98  
% 3.35/0.98  ------ AIG Options
% 3.35/0.98  
% 3.35/0.98  --aig_mode                              false
% 3.35/0.98  
% 3.35/0.98  ------ Instantiation Options
% 3.35/0.98  
% 3.35/0.98  --instantiation_flag                    true
% 3.35/0.98  --inst_sos_flag                         false
% 3.35/0.98  --inst_sos_phase                        true
% 3.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel_side                     num_symb
% 3.35/0.98  --inst_solver_per_active                1400
% 3.35/0.98  --inst_solver_calls_frac                1.
% 3.35/0.98  --inst_passive_queue_type               priority_queues
% 3.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.98  --inst_passive_queues_freq              [25;2]
% 3.35/0.98  --inst_dismatching                      true
% 3.35/0.98  --inst_eager_unprocessed_to_passive     true
% 3.35/0.98  --inst_prop_sim_given                   true
% 3.35/0.98  --inst_prop_sim_new                     false
% 3.35/0.98  --inst_subs_new                         false
% 3.35/0.98  --inst_eq_res_simp                      false
% 3.35/0.98  --inst_subs_given                       false
% 3.35/0.98  --inst_orphan_elimination               true
% 3.35/0.98  --inst_learning_loop_flag               true
% 3.35/0.98  --inst_learning_start                   3000
% 3.35/0.98  --inst_learning_factor                  2
% 3.35/0.98  --inst_start_prop_sim_after_learn       3
% 3.35/0.98  --inst_sel_renew                        solver
% 3.35/0.98  --inst_lit_activity_flag                true
% 3.35/0.98  --inst_restr_to_given                   false
% 3.35/0.98  --inst_activity_threshold               500
% 3.35/0.98  --inst_out_proof                        true
% 3.35/0.98  
% 3.35/0.98  ------ Resolution Options
% 3.35/0.98  
% 3.35/0.98  --resolution_flag                       true
% 3.35/0.98  --res_lit_sel                           adaptive
% 3.35/0.98  --res_lit_sel_side                      none
% 3.35/0.98  --res_ordering                          kbo
% 3.35/0.98  --res_to_prop_solver                    active
% 3.35/0.98  --res_prop_simpl_new                    false
% 3.35/0.98  --res_prop_simpl_given                  true
% 3.35/0.98  --res_passive_queue_type                priority_queues
% 3.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.98  --res_passive_queues_freq               [15;5]
% 3.35/0.98  --res_forward_subs                      full
% 3.35/0.98  --res_backward_subs                     full
% 3.35/0.98  --res_forward_subs_resolution           true
% 3.35/0.98  --res_backward_subs_resolution          true
% 3.35/0.98  --res_orphan_elimination                true
% 3.35/0.98  --res_time_limit                        2.
% 3.35/0.98  --res_out_proof                         true
% 3.35/0.98  
% 3.35/0.98  ------ Superposition Options
% 3.35/0.98  
% 3.35/0.98  --superposition_flag                    true
% 3.35/0.98  --sup_passive_queue_type                priority_queues
% 3.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.98  --demod_completeness_check              fast
% 3.35/0.98  --demod_use_ground                      true
% 3.35/0.98  --sup_to_prop_solver                    passive
% 3.35/0.98  --sup_prop_simpl_new                    true
% 3.35/0.98  --sup_prop_simpl_given                  true
% 3.35/0.98  --sup_fun_splitting                     false
% 3.35/0.98  --sup_smt_interval                      50000
% 3.35/0.98  
% 3.35/0.98  ------ Superposition Simplification Setup
% 3.35/0.98  
% 3.35/0.98  --sup_indices_passive                   []
% 3.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.98  --sup_full_bw                           [BwDemod]
% 3.35/0.98  --sup_immed_triv                        [TrivRules]
% 3.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.98  --sup_immed_bw_main                     []
% 3.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.98  
% 3.35/0.98  ------ Combination Options
% 3.35/0.98  
% 3.35/0.98  --comb_res_mult                         3
% 3.35/0.98  --comb_sup_mult                         2
% 3.35/0.98  --comb_inst_mult                        10
% 3.35/0.98  
% 3.35/0.98  ------ Debug Options
% 3.35/0.98  
% 3.35/0.98  --dbg_backtrace                         false
% 3.35/0.98  --dbg_dump_prop_clauses                 false
% 3.35/0.98  --dbg_dump_prop_clauses_file            -
% 3.35/0.98  --dbg_out_stat                          false
% 3.35/0.98  ------ Parsing...
% 3.35/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing... gs_s  sp: 14 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/0.98  ------ Proving...
% 3.35/0.98  ------ Problem Properties 
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  clauses                                 45
% 3.35/0.98  conjectures                             2
% 3.35/0.98  EPR                                     9
% 3.35/0.98  Horn                                    32
% 3.35/0.98  unary                                   7
% 3.35/0.98  binary                                  23
% 3.35/0.98  lits                                    101
% 3.35/0.98  lits eq                                 31
% 3.35/0.98  fd_pure                                 0
% 3.35/0.98  fd_pseudo                               0
% 3.35/0.98  fd_cond                                 1
% 3.35/0.98  fd_pseudo_cond                          4
% 3.35/0.98  AC symbols                              0
% 3.35/0.98  
% 3.35/0.98  ------ Schedule dynamic 5 is on 
% 3.35/0.98  
% 3.35/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  ------ 
% 3.35/0.98  Current options:
% 3.35/0.98  ------ 
% 3.35/0.98  
% 3.35/0.98  ------ Input Options
% 3.35/0.98  
% 3.35/0.98  --out_options                           all
% 3.35/0.98  --tptp_safe_out                         true
% 3.35/0.98  --problem_path                          ""
% 3.35/0.98  --include_path                          ""
% 3.35/0.98  --clausifier                            res/vclausify_rel
% 3.35/0.98  --clausifier_options                    --mode clausify
% 3.35/0.98  --stdin                                 false
% 3.35/0.98  --stats_out                             all
% 3.35/0.98  
% 3.35/0.98  ------ General Options
% 3.35/0.98  
% 3.35/0.98  --fof                                   false
% 3.35/0.98  --time_out_real                         305.
% 3.35/0.98  --time_out_virtual                      -1.
% 3.35/0.98  --symbol_type_check                     false
% 3.35/0.98  --clausify_out                          false
% 3.35/0.98  --sig_cnt_out                           false
% 3.35/0.98  --trig_cnt_out                          false
% 3.35/0.98  --trig_cnt_out_tolerance                1.
% 3.35/0.98  --trig_cnt_out_sk_spl                   false
% 3.35/0.98  --abstr_cl_out                          false
% 3.35/0.98  
% 3.35/0.98  ------ Global Options
% 3.35/0.98  
% 3.35/0.98  --schedule                              default
% 3.35/0.98  --add_important_lit                     false
% 3.35/0.98  --prop_solver_per_cl                    1000
% 3.35/0.98  --min_unsat_core                        false
% 3.35/0.98  --soft_assumptions                      false
% 3.35/0.98  --soft_lemma_size                       3
% 3.35/0.98  --prop_impl_unit_size                   0
% 3.35/0.98  --prop_impl_unit                        []
% 3.35/0.98  --share_sel_clauses                     true
% 3.35/0.98  --reset_solvers                         false
% 3.35/0.98  --bc_imp_inh                            [conj_cone]
% 3.35/0.98  --conj_cone_tolerance                   3.
% 3.35/0.98  --extra_neg_conj                        none
% 3.35/0.98  --large_theory_mode                     true
% 3.35/0.98  --prolific_symb_bound                   200
% 3.35/0.98  --lt_threshold                          2000
% 3.35/0.98  --clause_weak_htbl                      true
% 3.35/0.98  --gc_record_bc_elim                     false
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing Options
% 3.35/0.98  
% 3.35/0.98  --preprocessing_flag                    true
% 3.35/0.98  --time_out_prep_mult                    0.1
% 3.35/0.98  --splitting_mode                        input
% 3.35/0.98  --splitting_grd                         true
% 3.35/0.98  --splitting_cvd                         false
% 3.35/0.98  --splitting_cvd_svl                     false
% 3.35/0.98  --splitting_nvd                         32
% 3.35/0.98  --sub_typing                            true
% 3.35/0.98  --prep_gs_sim                           true
% 3.35/0.98  --prep_unflatten                        true
% 3.35/0.98  --prep_res_sim                          true
% 3.35/0.98  --prep_upred                            true
% 3.35/0.98  --prep_sem_filter                       exhaustive
% 3.35/0.98  --prep_sem_filter_out                   false
% 3.35/0.98  --pred_elim                             true
% 3.35/0.98  --res_sim_input                         true
% 3.35/0.98  --eq_ax_congr_red                       true
% 3.35/0.98  --pure_diseq_elim                       true
% 3.35/0.98  --brand_transform                       false
% 3.35/0.98  --non_eq_to_eq                          false
% 3.35/0.98  --prep_def_merge                        true
% 3.35/0.98  --prep_def_merge_prop_impl              false
% 3.35/0.98  --prep_def_merge_mbd                    true
% 3.35/0.98  --prep_def_merge_tr_red                 false
% 3.35/0.98  --prep_def_merge_tr_cl                  false
% 3.35/0.98  --smt_preprocessing                     true
% 3.35/0.98  --smt_ac_axioms                         fast
% 3.35/0.98  --preprocessed_out                      false
% 3.35/0.98  --preprocessed_stats                    false
% 3.35/0.98  
% 3.35/0.98  ------ Abstraction refinement Options
% 3.35/0.98  
% 3.35/0.98  --abstr_ref                             []
% 3.35/0.98  --abstr_ref_prep                        false
% 3.35/0.98  --abstr_ref_until_sat                   false
% 3.35/0.98  --abstr_ref_sig_restrict                funpre
% 3.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.98  --abstr_ref_under                       []
% 3.35/0.98  
% 3.35/0.98  ------ SAT Options
% 3.35/0.98  
% 3.35/0.98  --sat_mode                              false
% 3.35/0.98  --sat_fm_restart_options                ""
% 3.35/0.98  --sat_gr_def                            false
% 3.35/0.98  --sat_epr_types                         true
% 3.35/0.98  --sat_non_cyclic_types                  false
% 3.35/0.98  --sat_finite_models                     false
% 3.35/0.98  --sat_fm_lemmas                         false
% 3.35/0.98  --sat_fm_prep                           false
% 3.35/0.98  --sat_fm_uc_incr                        true
% 3.35/0.98  --sat_out_model                         small
% 3.35/0.98  --sat_out_clauses                       false
% 3.35/0.98  
% 3.35/0.98  ------ QBF Options
% 3.35/0.98  
% 3.35/0.98  --qbf_mode                              false
% 3.35/0.98  --qbf_elim_univ                         false
% 3.35/0.98  --qbf_dom_inst                          none
% 3.35/0.98  --qbf_dom_pre_inst                      false
% 3.35/0.98  --qbf_sk_in                             false
% 3.35/0.98  --qbf_pred_elim                         true
% 3.35/0.98  --qbf_split                             512
% 3.35/0.98  
% 3.35/0.98  ------ BMC1 Options
% 3.35/0.98  
% 3.35/0.98  --bmc1_incremental                      false
% 3.35/0.98  --bmc1_axioms                           reachable_all
% 3.35/0.98  --bmc1_min_bound                        0
% 3.35/0.98  --bmc1_max_bound                        -1
% 3.35/0.98  --bmc1_max_bound_default                -1
% 3.35/0.98  --bmc1_symbol_reachability              true
% 3.35/0.98  --bmc1_property_lemmas                  false
% 3.35/0.98  --bmc1_k_induction                      false
% 3.35/0.98  --bmc1_non_equiv_states                 false
% 3.35/0.98  --bmc1_deadlock                         false
% 3.35/0.98  --bmc1_ucm                              false
% 3.35/0.98  --bmc1_add_unsat_core                   none
% 3.35/0.98  --bmc1_unsat_core_children              false
% 3.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.98  --bmc1_out_stat                         full
% 3.35/0.98  --bmc1_ground_init                      false
% 3.35/0.98  --bmc1_pre_inst_next_state              false
% 3.35/0.98  --bmc1_pre_inst_state                   false
% 3.35/0.98  --bmc1_pre_inst_reach_state             false
% 3.35/0.98  --bmc1_out_unsat_core                   false
% 3.35/0.98  --bmc1_aig_witness_out                  false
% 3.35/0.98  --bmc1_verbose                          false
% 3.35/0.98  --bmc1_dump_clauses_tptp                false
% 3.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.98  --bmc1_dump_file                        -
% 3.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.98  --bmc1_ucm_extend_mode                  1
% 3.35/0.98  --bmc1_ucm_init_mode                    2
% 3.35/0.98  --bmc1_ucm_cone_mode                    none
% 3.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.98  --bmc1_ucm_relax_model                  4
% 3.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.98  --bmc1_ucm_layered_model                none
% 3.35/0.98  --bmc1_ucm_max_lemma_size               10
% 3.35/0.98  
% 3.35/0.98  ------ AIG Options
% 3.35/0.98  
% 3.35/0.98  --aig_mode                              false
% 3.35/0.98  
% 3.35/0.98  ------ Instantiation Options
% 3.35/0.98  
% 3.35/0.98  --instantiation_flag                    true
% 3.35/0.98  --inst_sos_flag                         false
% 3.35/0.98  --inst_sos_phase                        true
% 3.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel_side                     none
% 3.35/0.98  --inst_solver_per_active                1400
% 3.35/0.98  --inst_solver_calls_frac                1.
% 3.35/0.98  --inst_passive_queue_type               priority_queues
% 3.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.99  --inst_passive_queues_freq              [25;2]
% 3.35/0.99  --inst_dismatching                      true
% 3.35/0.99  --inst_eager_unprocessed_to_passive     true
% 3.35/0.99  --inst_prop_sim_given                   true
% 3.35/0.99  --inst_prop_sim_new                     false
% 3.35/0.99  --inst_subs_new                         false
% 3.35/0.99  --inst_eq_res_simp                      false
% 3.35/0.99  --inst_subs_given                       false
% 3.35/0.99  --inst_orphan_elimination               true
% 3.35/0.99  --inst_learning_loop_flag               true
% 3.35/0.99  --inst_learning_start                   3000
% 3.35/0.99  --inst_learning_factor                  2
% 3.35/0.99  --inst_start_prop_sim_after_learn       3
% 3.35/0.99  --inst_sel_renew                        solver
% 3.35/0.99  --inst_lit_activity_flag                true
% 3.35/0.99  --inst_restr_to_given                   false
% 3.35/0.99  --inst_activity_threshold               500
% 3.35/0.99  --inst_out_proof                        true
% 3.35/0.99  
% 3.35/0.99  ------ Resolution Options
% 3.35/0.99  
% 3.35/0.99  --resolution_flag                       false
% 3.35/0.99  --res_lit_sel                           adaptive
% 3.35/0.99  --res_lit_sel_side                      none
% 3.35/0.99  --res_ordering                          kbo
% 3.35/0.99  --res_to_prop_solver                    active
% 3.35/0.99  --res_prop_simpl_new                    false
% 3.35/0.99  --res_prop_simpl_given                  true
% 3.35/0.99  --res_passive_queue_type                priority_queues
% 3.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.99  --res_passive_queues_freq               [15;5]
% 3.35/0.99  --res_forward_subs                      full
% 3.35/0.99  --res_backward_subs                     full
% 3.35/0.99  --res_forward_subs_resolution           true
% 3.35/0.99  --res_backward_subs_resolution          true
% 3.35/0.99  --res_orphan_elimination                true
% 3.35/0.99  --res_time_limit                        2.
% 3.35/0.99  --res_out_proof                         true
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Options
% 3.35/0.99  
% 3.35/0.99  --superposition_flag                    true
% 3.35/0.99  --sup_passive_queue_type                priority_queues
% 3.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.99  --demod_completeness_check              fast
% 3.35/0.99  --demod_use_ground                      true
% 3.35/0.99  --sup_to_prop_solver                    passive
% 3.35/0.99  --sup_prop_simpl_new                    true
% 3.35/0.99  --sup_prop_simpl_given                  true
% 3.35/0.99  --sup_fun_splitting                     false
% 3.35/0.99  --sup_smt_interval                      50000
% 3.35/0.99  
% 3.35/0.99  ------ Superposition Simplification Setup
% 3.35/0.99  
% 3.35/0.99  --sup_indices_passive                   []
% 3.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_full_bw                           [BwDemod]
% 3.35/0.99  --sup_immed_triv                        [TrivRules]
% 3.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_immed_bw_main                     []
% 3.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.99  
% 3.35/0.99  ------ Combination Options
% 3.35/0.99  
% 3.35/0.99  --comb_res_mult                         3
% 3.35/0.99  --comb_sup_mult                         2
% 3.35/0.99  --comb_inst_mult                        10
% 3.35/0.99  
% 3.35/0.99  ------ Debug Options
% 3.35/0.99  
% 3.35/0.99  --dbg_backtrace                         false
% 3.35/0.99  --dbg_dump_prop_clauses                 false
% 3.35/0.99  --dbg_dump_prop_clauses_file            -
% 3.35/0.99  --dbg_out_stat                          false
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  ------ Proving...
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  % SZS status Theorem for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  fof(f9,axiom,(
% 3.35/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f20,plain,(
% 3.35/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.35/0.99    inference(ennf_transformation,[],[f9])).
% 3.35/0.99  
% 3.35/0.99  fof(f42,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.35/0.99    inference(nnf_transformation,[],[f20])).
% 3.35/0.99  
% 3.35/0.99  fof(f43,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.35/0.99    inference(rectify,[],[f42])).
% 3.35/0.99  
% 3.35/0.99  fof(f44,plain,(
% 3.35/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f45,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 3.35/0.99  
% 3.35/0.99  fof(f70,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f45])).
% 3.35/0.99  
% 3.35/0.99  fof(f11,axiom,(
% 3.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f23,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(ennf_transformation,[],[f11])).
% 3.35/0.99  
% 3.35/0.99  fof(f75,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f23])).
% 3.35/0.99  
% 3.35/0.99  fof(f15,conjecture,(
% 3.35/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f16,negated_conjecture,(
% 3.35/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.35/0.99    inference(negated_conjecture,[],[f15])).
% 3.35/0.99  
% 3.35/0.99  fof(f28,plain,(
% 3.35/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.35/0.99    inference(ennf_transformation,[],[f16])).
% 3.35/0.99  
% 3.35/0.99  fof(f29,plain,(
% 3.35/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.35/0.99    inference(flattening,[],[f28])).
% 3.35/0.99  
% 3.35/0.99  fof(f50,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f49,plain,(
% 3.35/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f51,plain,(
% 3.35/0.99    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f29,f50,f49])).
% 3.35/0.99  
% 3.35/0.99  fof(f86,plain,(
% 3.35/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.35/0.99    inference(cnf_transformation,[],[f51])).
% 3.35/0.99  
% 3.35/0.99  fof(f71,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f45])).
% 3.35/0.99  
% 3.35/0.99  fof(f10,axiom,(
% 3.35/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f21,plain,(
% 3.35/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.35/0.99    inference(ennf_transformation,[],[f10])).
% 3.35/0.99  
% 3.35/0.99  fof(f22,plain,(
% 3.35/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.35/0.99    inference(flattening,[],[f21])).
% 3.35/0.99  
% 3.35/0.99  fof(f46,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.35/0.99    inference(nnf_transformation,[],[f22])).
% 3.35/0.99  
% 3.35/0.99  fof(f47,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.35/0.99    inference(flattening,[],[f46])).
% 3.35/0.99  
% 3.35/0.99  fof(f72,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f47])).
% 3.35/0.99  
% 3.35/0.99  fof(f84,plain,(
% 3.35/0.99    v1_funct_1(sK8)),
% 3.35/0.99    inference(cnf_transformation,[],[f51])).
% 3.35/0.99  
% 3.35/0.99  fof(f85,plain,(
% 3.35/0.99    v1_funct_2(sK8,sK5,sK6)),
% 3.35/0.99    inference(cnf_transformation,[],[f51])).
% 3.35/0.99  
% 3.35/0.99  fof(f14,axiom,(
% 3.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f26,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(ennf_transformation,[],[f14])).
% 3.35/0.99  
% 3.35/0.99  fof(f27,plain,(
% 3.35/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(flattening,[],[f26])).
% 3.35/0.99  
% 3.35/0.99  fof(f48,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(nnf_transformation,[],[f27])).
% 3.35/0.99  
% 3.35/0.99  fof(f78,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f48])).
% 3.35/0.99  
% 3.35/0.99  fof(f12,axiom,(
% 3.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f24,plain,(
% 3.35/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(ennf_transformation,[],[f12])).
% 3.35/0.99  
% 3.35/0.99  fof(f76,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f24])).
% 3.35/0.99  
% 3.35/0.99  fof(f68,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f45])).
% 3.35/0.99  
% 3.35/0.99  fof(f13,axiom,(
% 3.35/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f25,plain,(
% 3.35/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.99    inference(ennf_transformation,[],[f13])).
% 3.35/0.99  
% 3.35/0.99  fof(f77,plain,(
% 3.35/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f25])).
% 3.35/0.99  
% 3.35/0.99  fof(f87,plain,(
% 3.35/0.99    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 3.35/0.99    inference(cnf_transformation,[],[f51])).
% 3.35/0.99  
% 3.35/0.99  fof(f69,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f45])).
% 3.35/0.99  
% 3.35/0.99  fof(f73,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f47])).
% 3.35/0.99  
% 3.35/0.99  fof(f88,plain,(
% 3.35/0.99    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f51])).
% 3.35/0.99  
% 3.35/0.99  fof(f4,axiom,(
% 3.35/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f40,plain,(
% 3.35/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.35/0.99    inference(nnf_transformation,[],[f4])).
% 3.35/0.99  
% 3.35/0.99  fof(f41,plain,(
% 3.35/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.35/0.99    inference(flattening,[],[f40])).
% 3.35/0.99  
% 3.35/0.99  fof(f63,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.35/0.99    inference(cnf_transformation,[],[f41])).
% 3.35/0.99  
% 3.35/0.99  fof(f92,plain,(
% 3.35/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.35/0.99    inference(equality_resolution,[],[f63])).
% 3.35/0.99  
% 3.35/0.99  fof(f79,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f48])).
% 3.35/0.99  
% 3.35/0.99  fof(f99,plain,(
% 3.35/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.35/0.99    inference(equality_resolution,[],[f79])).
% 3.35/0.99  
% 3.35/0.99  fof(f62,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.35/0.99    inference(cnf_transformation,[],[f41])).
% 3.35/0.99  
% 3.35/0.99  fof(f93,plain,(
% 3.35/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.35/0.99    inference(equality_resolution,[],[f62])).
% 3.35/0.99  
% 3.35/0.99  fof(f1,axiom,(
% 3.35/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f30,plain,(
% 3.35/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.35/0.99    inference(nnf_transformation,[],[f1])).
% 3.35/0.99  
% 3.35/0.99  fof(f31,plain,(
% 3.35/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.35/0.99    inference(rectify,[],[f30])).
% 3.35/0.99  
% 3.35/0.99  fof(f32,plain,(
% 3.35/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.35/0.99    introduced(choice_axiom,[])).
% 3.35/0.99  
% 3.35/0.99  fof(f33,plain,(
% 3.35/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.35/0.99  
% 3.35/0.99  fof(f52,plain,(
% 3.35/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f8,axiom,(
% 3.35/0.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f19,plain,(
% 3.35/0.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.35/0.99    inference(ennf_transformation,[],[f8])).
% 3.35/0.99  
% 3.35/0.99  fof(f67,plain,(
% 3.35/0.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f19])).
% 3.35/0.99  
% 3.35/0.99  fof(f53,plain,(
% 3.35/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f33])).
% 3.35/0.99  
% 3.35/0.99  fof(f82,plain,(
% 3.35/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.99    inference(cnf_transformation,[],[f48])).
% 3.35/0.99  
% 3.35/0.99  fof(f97,plain,(
% 3.35/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.35/0.99    inference(equality_resolution,[],[f82])).
% 3.35/0.99  
% 3.35/0.99  fof(f2,axiom,(
% 3.35/0.99    v1_xboole_0(k1_xboole_0)),
% 3.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.99  
% 3.35/0.99  fof(f54,plain,(
% 3.35/0.99    v1_xboole_0(k1_xboole_0)),
% 3.35/0.99    inference(cnf_transformation,[],[f2])).
% 3.35/0.99  
% 3.35/0.99  fof(f61,plain,(
% 3.35/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.35/0.99    inference(cnf_transformation,[],[f41])).
% 3.35/0.99  
% 3.35/0.99  cnf(c_17,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.35/0.99      | r2_hidden(sK4(X0,X2,X1),X2)
% 3.35/0.99      | ~ v1_relat_1(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_23,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | v1_relat_1(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_34,negated_conjecture,
% 3.35/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.35/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_610,plain,
% 3.35/0.99      ( v1_relat_1(X0)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_611,plain,
% 3.35/0.99      ( v1_relat_1(sK8)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_610]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_924,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.35/0.99      | r2_hidden(sK4(X0,X2,X1),X2)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_611]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_925,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),X1)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_924]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1371,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),X1)
% 3.35/0.99      | ~ sP2_iProver_split ),
% 3.35/0.99      inference(splitting,
% 3.35/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.35/0.99                [c_925]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1922,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),X1) = iProver_top
% 3.35/0.99      | sP2_iProver_split != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1372,plain,
% 3.35/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 3.35/0.99      inference(splitting,
% 3.35/0.99                [splitting(split),new_symbols(definition,[])],
% 3.35/0.99                [c_925]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1417,plain,
% 3.35/0.99      ( sP2_iProver_split = iProver_top
% 3.35/0.99      | sP0_iProver_split = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1372]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1418,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),X1) = iProver_top
% 3.35/0.99      | sP2_iProver_split != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1384,plain,( X0 = X0 ),theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2209,plain,
% 3.35/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1384]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_16,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,X1)
% 3.35/0.99      | r2_hidden(X2,k9_relat_1(X3,X1))
% 3.35/0.99      | ~ r2_hidden(X0,k1_relat_1(X3))
% 3.35/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.35/0.99      | ~ v1_relat_1(X3) ),
% 3.35/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_939,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,X1)
% 3.35/0.99      | r2_hidden(X2,k9_relat_1(X3,X1))
% 3.35/0.99      | ~ r2_hidden(X0,k1_relat_1(X3))
% 3.35/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X4,X5)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X3 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_611]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_940,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,X1)
% 3.35/0.99      | r2_hidden(X2,k9_relat_1(sK8,X1))
% 3.35/0.99      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 3.35/0.99      | ~ r2_hidden(k4_tarski(X0,X2),sK8)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_939]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_22,plain,
% 3.35/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 3.35/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.35/0.99      | ~ v1_funct_1(X1)
% 3.35/0.99      | ~ v1_relat_1(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_36,negated_conjecture,
% 3.35/0.99      ( v1_funct_1(sK8) ),
% 3.35/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_381,plain,
% 3.35/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 3.35/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.35/0.99      | ~ v1_relat_1(X1)
% 3.35/0.99      | sK8 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_382,plain,
% 3.35/0.99      ( r2_hidden(X0,k1_relat_1(sK8))
% 3.35/0.99      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.35/0.99      | ~ v1_relat_1(sK8) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_381]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_804,plain,
% 3.35/0.99      ( r2_hidden(X0,k1_relat_1(sK8))
% 3.35/0.99      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(resolution,[status(thm)],[c_611,c_382]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_947,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,X1)
% 3.35/0.99      | r2_hidden(X2,k9_relat_1(sK8,X1))
% 3.35/0.99      | ~ r2_hidden(k4_tarski(X0,X2),sK8)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(forward_subsumption_resolution,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_940,c_804]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1368,plain,
% 3.35/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | ~ sP0_iProver_split ),
% 3.35/0.99      inference(splitting,
% 3.35/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.35/0.99                [c_947]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2210,plain,
% 3.35/0.99      ( ~ sP0_iProver_split
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1368]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2213,plain,
% 3.35/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sP0_iProver_split != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2210]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2738,plain,
% 3.35/0.99      ( r2_hidden(sK4(X0,X1,sK8),X1) = iProver_top
% 3.35/0.99      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1922,c_1417,c_1418,c_2209,c_2213]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2739,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),X1) = iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_2738]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_35,negated_conjecture,
% 3.35/0.99      ( v1_funct_2(sK8,sK5,sK6) ),
% 3.35/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_31,plain,
% 3.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.35/0.99      | k1_xboole_0 = X2 ),
% 3.35/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_556,plain,
% 3.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X0
% 3.35/0.99      | k1_xboole_0 = X2 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_557,plain,
% 3.35/0.99      ( ~ v1_funct_2(sK8,X0,X1)
% 3.35/0.99      | k1_relset_1(X0,X1,sK8) = X0
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | k1_xboole_0 = X1 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_556]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1084,plain,
% 3.35/0.99      ( k1_relset_1(X0,X1,sK8) = X0
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK6 != X1
% 3.35/0.99      | sK5 != X0
% 3.35/0.99      | sK8 != sK8
% 3.35/0.99      | k1_xboole_0 = X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_557]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1085,plain,
% 3.35/0.99      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | k1_xboole_0 = sK6 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1084]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1160,plain,
% 3.35/0.99      ( k1_relset_1(sK5,sK6,sK8) = sK5 | k1_xboole_0 = sK6 ),
% 3.35/0.99      inference(equality_resolution_simp,[status(thm)],[c_1085]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_24,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_601,plain,
% 3.35/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X2 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_602,plain,
% 3.35/0.99      ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_601]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2200,plain,
% 3.35/0.99      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.35/0.99      inference(equality_resolution,[status(thm)],[c_602]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2270,plain,
% 3.35/0.99      ( k1_relat_1(sK8) = sK5 | sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_1160,c_2200]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_19,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.35/0.99      | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
% 3.35/0.99      | ~ v1_relat_1(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_894,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.35/0.99      | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_611]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_895,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8))
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_894]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1375,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8))
% 3.35/0.99      | ~ sP4_iProver_split ),
% 3.35/0.99      inference(splitting,
% 3.35/0.99                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 3.35/0.99                [c_895]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1928,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8)) = iProver_top
% 3.35/0.99      | sP4_iProver_split != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1376,plain,
% 3.35/0.99      ( sP4_iProver_split | sP0_iProver_split ),
% 3.35/0.99      inference(splitting,
% 3.35/0.99                [splitting(split),new_symbols(definition,[])],
% 3.35/0.99                [c_895]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1427,plain,
% 3.35/0.99      ( sP4_iProver_split = iProver_top
% 3.35/0.99      | sP0_iProver_split = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1376]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1428,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8)) = iProver_top
% 3.35/0.99      | sP4_iProver_split != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2850,plain,
% 3.35/0.99      ( r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8)) = iProver_top
% 3.35/0.99      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1928,c_1427,c_1428,c_2209,c_2213]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2851,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),k1_relat_1(sK8)) = iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_2850]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2858,plain,
% 3.35/0.99      ( sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(sK4(X0,X1,sK8),sK5) = iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2270,c_2851]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_25,plain,
% 3.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.35/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_592,plain,
% 3.35/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X2 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_593,plain,
% 3.35/0.99      ( k7_relset_1(X0,X1,sK8,X2) = k9_relat_1(sK8,X2)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_592]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2203,plain,
% 3.35/0.99      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.35/0.99      inference(equality_resolution,[status(thm)],[c_593]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_33,negated_conjecture,
% 3.35/0.99      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.35/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1942,plain,
% 3.35/0.99      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2217,plain,
% 3.35/0.99      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_2203,c_1942]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_18,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.35/0.99      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
% 3.35/0.99      | ~ v1_relat_1(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_909,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.35/0.99      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_611]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_910,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
% 3.35/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_909]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1373,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
% 3.35/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8)
% 3.35/0.99      | ~ sP3_iProver_split ),
% 3.35/0.99      inference(splitting,
% 3.35/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 3.35/0.99                [c_910]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1925,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8) = iProver_top
% 3.35/0.99      | sP3_iProver_split != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1373]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1374,plain,
% 3.35/0.99      ( sP3_iProver_split | sP0_iProver_split ),
% 3.35/0.99      inference(splitting,
% 3.35/0.99                [splitting(split),new_symbols(definition,[])],
% 3.35/0.99                [c_910]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1422,plain,
% 3.35/0.99      ( sP3_iProver_split = iProver_top
% 3.35/0.99      | sP0_iProver_split = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1374]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1423,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8) = iProver_top
% 3.35/0.99      | sP3_iProver_split != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1373]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2878,plain,
% 3.35/0.99      ( r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8) = iProver_top
% 3.35/0.99      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1925,c_1422,c_1423,c_2209,c_2213]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2879,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | r2_hidden(k4_tarski(sK4(X0,X1,sK8),X0),sK8) = iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_2878]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_21,plain,
% 3.35/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.35/0.99      | ~ v1_funct_1(X2)
% 3.35/0.99      | ~ v1_relat_1(X2)
% 3.35/0.99      | k1_funct_1(X2,X0) = X1 ),
% 3.35/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_411,plain,
% 3.35/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.35/0.99      | ~ v1_relat_1(X2)
% 3.35/0.99      | k1_funct_1(X2,X0) = X1
% 3.35/0.99      | sK8 != X2 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_412,plain,
% 3.35/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.35/0.99      | ~ v1_relat_1(sK8)
% 3.35/0.99      | k1_funct_1(sK8,X0) = X1 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_411]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_776,plain,
% 3.35/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.35/0.99      | k1_funct_1(sK8,X0) = X1
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(resolution,[status(thm)],[c_611,c_412]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1381,plain,
% 3.35/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.35/0.99      | k1_funct_1(sK8,X0) = X1
% 3.35/0.99      | ~ sP7_iProver_split ),
% 3.35/0.99      inference(splitting,
% 3.35/0.99                [splitting(split),new_symbols(definition,[sP7_iProver_split])],
% 3.35/0.99                [c_776]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1939,plain,
% 3.35/0.99      ( k1_funct_1(sK8,X0) = X1
% 3.35/0.99      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.35/0.99      | sP7_iProver_split != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1382,plain,
% 3.35/0.99      ( sP7_iProver_split | sP0_iProver_split ),
% 3.35/0.99      inference(splitting,
% 3.35/0.99                [splitting(split),new_symbols(definition,[])],
% 3.35/0.99                [c_776]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1444,plain,
% 3.35/0.99      ( sP7_iProver_split = iProver_top
% 3.35/0.99      | sP0_iProver_split = iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1382]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1445,plain,
% 3.35/0.99      ( k1_funct_1(sK8,X0) = X1
% 3.35/0.99      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.35/0.99      | sP7_iProver_split != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2540,plain,
% 3.35/0.99      ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.35/0.99      | k1_funct_1(sK8,X0) = X1 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_1939,c_1444,c_1445,c_2209,c_2213]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2541,plain,
% 3.35/0.99      ( k1_funct_1(sK8,X0) = X1
% 3.35/0.99      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_2540]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2888,plain,
% 3.35/0.99      ( k1_funct_1(sK8,sK4(X0,X1,sK8)) = X0
% 3.35/0.99      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2879,c_2541]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4958,plain,
% 3.35/0.99      ( k1_funct_1(sK8,sK4(sK9,sK7,sK8)) = sK9 ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2217,c_2888]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_32,negated_conjecture,
% 3.35/0.99      ( ~ r2_hidden(X0,sK5)
% 3.35/0.99      | ~ r2_hidden(X0,sK7)
% 3.35/0.99      | k1_funct_1(sK8,X0) != sK9 ),
% 3.35/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1943,plain,
% 3.35/0.99      ( k1_funct_1(sK8,X0) != sK9
% 3.35/0.99      | r2_hidden(X0,sK5) != iProver_top
% 3.35/0.99      | r2_hidden(X0,sK7) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5002,plain,
% 3.35/0.99      ( r2_hidden(sK4(sK9,sK7,sK8),sK5) != iProver_top
% 3.35/0.99      | r2_hidden(sK4(sK9,sK7,sK8),sK7) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_4958,c_1943]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6090,plain,
% 3.35/0.99      ( sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(sK4(sK9,sK7,sK8),sK7) != iProver_top
% 3.35/0.99      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2858,c_5002]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6885,plain,
% 3.35/0.99      ( r2_hidden(sK4(sK9,sK7,sK8),sK7) != iProver_top
% 3.35/0.99      | sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_6090,c_2217]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6886,plain,
% 3.35/0.99      ( sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(sK4(sK9,sK7,sK8),sK7) != iProver_top ),
% 3.35/0.99      inference(renaming,[status(thm)],[c_6885]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6891,plain,
% 3.35/0.99      ( sK6 = k1_xboole_0
% 3.35/0.99      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2739,c_6886]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6894,plain,
% 3.35/0.99      ( sK6 = k1_xboole_0 ),
% 3.35/0.99      inference(global_propositional_subsumption,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_6891,c_2217]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_9,plain,
% 3.35/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2275,plain,
% 3.35/0.99      ( k1_relset_1(X0,k1_xboole_0,sK8) = k1_relat_1(sK8)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k1_xboole_0) ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_9,c_602]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6904,plain,
% 3.35/0.99      ( k1_relset_1(X0,k1_xboole_0,sK8) = k1_relat_1(sK8)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_6894,c_2275]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6933,plain,
% 3.35/0.99      ( k1_relset_1(X0,k1_xboole_0,sK8) = k1_relat_1(sK8)
% 3.35/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_6904,c_9]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6934,plain,
% 3.35/0.99      ( k1_relset_1(X0,k1_xboole_0,sK8) = k1_relat_1(sK8) ),
% 3.35/0.99      inference(equality_resolution_simp,[status(thm)],[c_6933]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_30,plain,
% 3.35/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.35/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_657,plain,
% 3.35/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.35/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_658,plain,
% 3.35/0.99      ( ~ v1_funct_2(sK8,k1_xboole_0,X0)
% 3.35/0.99      | k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_657]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1109,plain,
% 3.35/0.99      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK6 != X0
% 3.35/0.99      | sK5 != k1_xboole_0
% 3.35/0.99      | sK8 != sK8 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_658]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1110,plain,
% 3.35/0.99      ( k1_relset_1(k1_xboole_0,sK6,sK8) = k1_xboole_0
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK5 != k1_xboole_0 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1109]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_10,plain,
% 3.35/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2072,plain,
% 3.35/0.99      ( k1_relset_1(k1_xboole_0,sK6,sK8) = k1_xboole_0
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k1_xboole_0)
% 3.35/0.99      | sK5 != k1_xboole_0 ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_1110,c_10]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6905,plain,
% 3.35/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 3.35/0.99      | sK5 != k1_xboole_0 ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_6894,c_2072]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6927,plain,
% 3.35/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
% 3.35/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 3.35/0.99      | sK5 != k1_xboole_0 ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_6905,c_9]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6928,plain,
% 3.35/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
% 3.35/0.99      | sK5 != k1_xboole_0 ),
% 3.35/0.99      inference(equality_resolution_simp,[status(thm)],[c_6927]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_6935,plain,
% 3.35/0.99      ( k1_relat_1(sK8) = k1_xboole_0 | sK5 != k1_xboole_0 ),
% 3.35/0.99      inference(demodulation,[status(thm)],[c_6934,c_6928]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1386,plain,
% 3.35/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.35/0.99      theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5487,plain,
% 3.35/0.99      ( ~ v1_xboole_0(X0)
% 3.35/0.99      | v1_xboole_0(k1_relat_1(sK8))
% 3.35/0.99      | k1_relat_1(sK8) != X0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1386]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5489,plain,
% 3.35/0.99      ( v1_xboole_0(k1_relat_1(sK8))
% 3.35/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.35/0.99      | k1_relat_1(sK8) != k1_xboole_0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_5487]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1390,plain,
% 3.35/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.35/0.99      theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2239,plain,
% 3.35/0.99      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK5,sK6)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1390]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_5283,plain,
% 3.35/0.99      ( k2_zfmisc_1(sK5,k1_xboole_0) != k2_zfmisc_1(sK5,sK6)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2239]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.35/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1952,plain,
% 3.35/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.35/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3217,plain,
% 3.35/0.99      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.35/0.99      | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2851,c_1952]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4528,plain,
% 3.35/0.99      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.35/0.99      inference(superposition,[status(thm)],[c_2217,c_3217]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_4533,plain,
% 3.35/0.99      ( ~ v1_xboole_0(k1_relat_1(sK8)) ),
% 3.35/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4528]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_15,plain,
% 3.35/0.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_833,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.35/0.99      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
% 3.35/0.99      | ~ v1_xboole_0(X3)
% 3.35/0.99      | X1 != X3 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_834,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.35/0.99      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
% 3.35/0.99      | ~ v1_xboole_0(X1) ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_833]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_844,plain,
% 3.35/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2)) | ~ v1_xboole_0(X1) ),
% 3.35/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_834,c_1]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_3507,plain,
% 3.35/0.99      ( ~ r2_hidden(sK0(k9_relat_1(sK8,sK7)),k9_relat_1(sK8,sK7))
% 3.35/0.99      | ~ v1_xboole_0(sK8) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_844]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1389,plain,
% 3.35/0.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.35/0.99      theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2350,plain,
% 3.35/0.99      ( X0 != sK6
% 3.35/0.99      | X1 != sK5
% 3.35/0.99      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK5,sK6) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1389]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2614,plain,
% 3.35/0.99      ( X0 != sK5
% 3.35/0.99      | k2_zfmisc_1(X0,k1_xboole_0) = k2_zfmisc_1(sK5,sK6)
% 3.35/0.99      | k1_xboole_0 != sK6 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2350]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2942,plain,
% 3.35/0.99      ( k2_zfmisc_1(sK5,k1_xboole_0) = k2_zfmisc_1(sK5,sK6)
% 3.35/0.99      | sK5 != sK5
% 3.35/0.99      | k1_xboole_0 != sK6 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2614]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_0,plain,
% 3.35/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2781,plain,
% 3.35/0.99      ( r2_hidden(sK0(k9_relat_1(sK8,sK7)),k9_relat_1(sK8,sK7))
% 3.35/0.99      | v1_xboole_0(k9_relat_1(sK8,sK7)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1385,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2621,plain,
% 3.35/0.99      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1385]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2622,plain,
% 3.35/0.99      ( sK6 != k1_xboole_0
% 3.35/0.99      | k1_xboole_0 = sK6
% 3.35/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2621]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2211,plain,
% 3.35/0.99      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_593]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2502,plain,
% 3.35/0.99      ( k7_relset_1(sK5,sK6,sK8,sK7) = k9_relat_1(sK8,sK7)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2211]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2300,plain,
% 3.35/0.99      ( ~ v1_xboole_0(X0)
% 3.35/0.99      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7))
% 3.35/0.99      | k7_relset_1(sK5,sK6,sK8,sK7) != X0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1386]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2501,plain,
% 3.35/0.99      ( v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7))
% 3.35/0.99      | ~ v1_xboole_0(k9_relat_1(sK8,sK7))
% 3.35/0.99      | k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2300]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2345,plain,
% 3.35/0.99      ( sK5 = sK5 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1384]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2259,plain,
% 3.35/0.99      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1385]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2344,plain,
% 3.35/0.99      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2259]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2234,plain,
% 3.35/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK8) | sK8 != X0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1386]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2236,plain,
% 3.35/0.99      ( v1_xboole_0(sK8)
% 3.35/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.35/0.99      | sK8 != k1_xboole_0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_2234]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2225,plain,
% 3.35/0.99      ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.35/0.99      | ~ v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_27,plain,
% 3.35/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.35/0.99      | k1_xboole_0 = X1
% 3.35/0.99      | k1_xboole_0 = X0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_639,plain,
% 3.35/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK8 != X0
% 3.35/0.99      | k1_xboole_0 = X0
% 3.35/0.99      | k1_xboole_0 = X1 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_640,plain,
% 3.35/0.99      ( ~ v1_funct_2(sK8,X0,k1_xboole_0)
% 3.35/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | k1_xboole_0 = X0
% 3.35/0.99      | k1_xboole_0 = sK8 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_639]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1095,plain,
% 3.35/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK6 != k1_xboole_0
% 3.35/0.99      | sK5 != X0
% 3.35/0.99      | sK8 != sK8
% 3.35/0.99      | sK8 = k1_xboole_0
% 3.35/0.99      | k1_xboole_0 = X0 ),
% 3.35/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_640]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_1096,plain,
% 3.35/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.35/0.99      | sK6 != k1_xboole_0
% 3.35/0.99      | sK8 = k1_xboole_0
% 3.35/0.99      | k1_xboole_0 = sK5 ),
% 3.35/0.99      inference(unflattening,[status(thm)],[c_1095]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_2,plain,
% 3.35/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.35/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_103,plain,
% 3.35/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_11,plain,
% 3.35/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.35/0.99      | k1_xboole_0 = X1
% 3.35/0.99      | k1_xboole_0 = X0 ),
% 3.35/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(c_102,plain,
% 3.35/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.35/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.35/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.35/0.99  
% 3.35/0.99  cnf(contradiction,plain,
% 3.35/0.99      ( $false ),
% 3.35/0.99      inference(minisat,
% 3.35/0.99                [status(thm)],
% 3.35/0.99                [c_6935,c_6891,c_5489,c_5283,c_4533,c_3507,c_2942,c_2781,
% 3.35/0.99                 c_2622,c_2502,c_2501,c_2345,c_2344,c_2236,c_2225,c_2217,
% 3.35/0.99                 c_2209,c_1096,c_2,c_103,c_102,c_33]) ).
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/0.99  
% 3.35/0.99  ------                               Statistics
% 3.35/0.99  
% 3.35/0.99  ------ General
% 3.35/0.99  
% 3.35/0.99  abstr_ref_over_cycles:                  0
% 3.35/0.99  abstr_ref_under_cycles:                 0
% 3.35/0.99  gc_basic_clause_elim:                   0
% 3.35/0.99  forced_gc_time:                         0
% 3.35/0.99  parsing_time:                           0.019
% 3.35/0.99  unif_index_cands_time:                  0.
% 3.35/0.99  unif_index_add_time:                    0.
% 3.35/0.99  orderings_time:                         0.
% 3.35/0.99  out_proof_time:                         0.015
% 3.35/0.99  total_time:                             0.228
% 3.35/0.99  num_of_symbols:                         65
% 3.35/0.99  num_of_terms:                           7711
% 3.35/0.99  
% 3.35/0.99  ------ Preprocessing
% 3.35/0.99  
% 3.35/0.99  num_of_splits:                          14
% 3.35/0.99  num_of_split_atoms:                     8
% 3.35/0.99  num_of_reused_defs:                     6
% 3.35/0.99  num_eq_ax_congr_red:                    39
% 3.35/0.99  num_of_sem_filtered_clauses:            1
% 3.35/0.99  num_of_subtypes:                        0
% 3.35/0.99  monotx_restored_types:                  0
% 3.35/0.99  sat_num_of_epr_types:                   0
% 3.35/0.99  sat_num_of_non_cyclic_types:            0
% 3.35/0.99  sat_guarded_non_collapsed_types:        0
% 3.35/0.99  num_pure_diseq_elim:                    0
% 3.35/0.99  simp_replaced_by:                       0
% 3.35/0.99  res_preprocessed:                       175
% 3.35/0.99  prep_upred:                             0
% 3.35/0.99  prep_unflattend:                        63
% 3.35/0.99  smt_new_axioms:                         0
% 3.35/0.99  pred_elim_cands:                        2
% 3.35/0.99  pred_elim:                              4
% 3.35/0.99  pred_elim_cl:                           6
% 3.35/0.99  pred_elim_cycles:                       9
% 3.35/0.99  merged_defs:                            0
% 3.35/0.99  merged_defs_ncl:                        0
% 3.35/0.99  bin_hyper_res:                          0
% 3.35/0.99  prep_cycles:                            4
% 3.35/0.99  pred_elim_time:                         0.021
% 3.35/0.99  splitting_time:                         0.
% 3.35/0.99  sem_filter_time:                        0.
% 3.35/0.99  monotx_time:                            0.
% 3.35/0.99  subtype_inf_time:                       0.
% 3.35/0.99  
% 3.35/0.99  ------ Problem properties
% 3.35/0.99  
% 3.35/0.99  clauses:                                45
% 3.35/0.99  conjectures:                            2
% 3.35/0.99  epr:                                    9
% 3.35/0.99  horn:                                   32
% 3.35/0.99  ground:                                 13
% 3.35/0.99  unary:                                  7
% 3.35/0.99  binary:                                 23
% 3.35/0.99  lits:                                   101
% 3.35/0.99  lits_eq:                                31
% 3.35/0.99  fd_pure:                                0
% 3.35/0.99  fd_pseudo:                              0
% 3.35/0.99  fd_cond:                                1
% 3.35/0.99  fd_pseudo_cond:                         4
% 3.35/0.99  ac_symbols:                             0
% 3.35/0.99  
% 3.35/0.99  ------ Propositional Solver
% 3.35/0.99  
% 3.35/0.99  prop_solver_calls:                      28
% 3.35/0.99  prop_fast_solver_calls:                 1197
% 3.35/0.99  smt_solver_calls:                       0
% 3.35/0.99  smt_fast_solver_calls:                  0
% 3.35/0.99  prop_num_of_clauses:                    2667
% 3.35/0.99  prop_preprocess_simplified:             7088
% 3.35/0.99  prop_fo_subsumed:                       20
% 3.35/0.99  prop_solver_time:                       0.
% 3.35/0.99  smt_solver_time:                        0.
% 3.35/0.99  smt_fast_solver_time:                   0.
% 3.35/0.99  prop_fast_solver_time:                  0.
% 3.35/0.99  prop_unsat_core_time:                   0.
% 3.35/0.99  
% 3.35/0.99  ------ QBF
% 3.35/0.99  
% 3.35/0.99  qbf_q_res:                              0
% 3.35/0.99  qbf_num_tautologies:                    0
% 3.35/0.99  qbf_prep_cycles:                        0
% 3.35/0.99  
% 3.35/0.99  ------ BMC1
% 3.35/0.99  
% 3.35/0.99  bmc1_current_bound:                     -1
% 3.35/0.99  bmc1_last_solved_bound:                 -1
% 3.35/0.99  bmc1_unsat_core_size:                   -1
% 3.35/0.99  bmc1_unsat_core_parents_size:           -1
% 3.35/0.99  bmc1_merge_next_fun:                    0
% 3.35/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.35/0.99  
% 3.35/0.99  ------ Instantiation
% 3.35/0.99  
% 3.35/0.99  inst_num_of_clauses:                    831
% 3.35/0.99  inst_num_in_passive:                    119
% 3.35/0.99  inst_num_in_active:                     331
% 3.35/0.99  inst_num_in_unprocessed:                381
% 3.35/0.99  inst_num_of_loops:                      390
% 3.35/0.99  inst_num_of_learning_restarts:          0
% 3.35/0.99  inst_num_moves_active_passive:          55
% 3.35/0.99  inst_lit_activity:                      0
% 3.35/0.99  inst_lit_activity_moves:                0
% 3.35/0.99  inst_num_tautologies:                   0
% 3.35/0.99  inst_num_prop_implied:                  0
% 3.35/0.99  inst_num_existing_simplified:           0
% 3.35/0.99  inst_num_eq_res_simplified:             0
% 3.35/0.99  inst_num_child_elim:                    0
% 3.35/0.99  inst_num_of_dismatching_blockings:      166
% 3.35/0.99  inst_num_of_non_proper_insts:           541
% 3.35/0.99  inst_num_of_duplicates:                 0
% 3.35/0.99  inst_inst_num_from_inst_to_res:         0
% 3.35/0.99  inst_dismatching_checking_time:         0.
% 3.35/0.99  
% 3.35/0.99  ------ Resolution
% 3.35/0.99  
% 3.35/0.99  res_num_of_clauses:                     0
% 3.35/0.99  res_num_in_passive:                     0
% 3.35/0.99  res_num_in_active:                      0
% 3.35/0.99  res_num_of_loops:                       179
% 3.35/0.99  res_forward_subset_subsumed:            32
% 3.35/0.99  res_backward_subset_subsumed:           2
% 3.35/0.99  res_forward_subsumed:                   4
% 3.35/0.99  res_backward_subsumed:                  1
% 3.35/0.99  res_forward_subsumption_resolution:     4
% 3.35/0.99  res_backward_subsumption_resolution:    0
% 3.35/0.99  res_clause_to_clause_subsumption:       505
% 3.35/0.99  res_orphan_elimination:                 0
% 3.35/0.99  res_tautology_del:                      45
% 3.35/0.99  res_num_eq_res_simplified:              1
% 3.35/0.99  res_num_sel_changes:                    0
% 3.35/0.99  res_moves_from_active_to_pass:          0
% 3.35/0.99  
% 3.35/0.99  ------ Superposition
% 3.35/0.99  
% 3.35/0.99  sup_time_total:                         0.
% 3.35/0.99  sup_time_generating:                    0.
% 3.35/0.99  sup_time_sim_full:                      0.
% 3.35/0.99  sup_time_sim_immed:                     0.
% 3.35/0.99  
% 3.35/0.99  sup_num_of_clauses:                     141
% 3.35/0.99  sup_num_in_active:                      59
% 3.35/0.99  sup_num_in_passive:                     82
% 3.35/0.99  sup_num_of_loops:                       77
% 3.35/0.99  sup_fw_superposition:                   109
% 3.35/0.99  sup_bw_superposition:                   41
% 3.35/0.99  sup_immediate_simplified:               39
% 3.35/0.99  sup_given_eliminated:                   1
% 3.35/0.99  comparisons_done:                       0
% 3.35/0.99  comparisons_avoided:                    3
% 3.35/0.99  
% 3.35/0.99  ------ Simplifications
% 3.35/0.99  
% 3.35/0.99  
% 3.35/0.99  sim_fw_subset_subsumed:                 10
% 3.35/0.99  sim_bw_subset_subsumed:                 4
% 3.35/0.99  sim_fw_subsumed:                        15
% 3.35/0.99  sim_bw_subsumed:                        3
% 3.35/0.99  sim_fw_subsumption_res:                 0
% 3.35/0.99  sim_bw_subsumption_res:                 0
% 3.35/0.99  sim_tautology_del:                      2
% 3.35/0.99  sim_eq_tautology_del:                   2
% 3.35/0.99  sim_eq_res_simp:                        7
% 3.35/0.99  sim_fw_demodulated:                     15
% 3.35/0.99  sim_bw_demodulated:                     15
% 3.35/0.99  sim_light_normalised:                   0
% 3.35/0.99  sim_joinable_taut:                      0
% 3.35/0.99  sim_joinable_simp:                      0
% 3.35/0.99  sim_ac_normalised:                      0
% 3.35/0.99  sim_smt_subsumption:                    0
% 3.35/0.99  
%------------------------------------------------------------------------------

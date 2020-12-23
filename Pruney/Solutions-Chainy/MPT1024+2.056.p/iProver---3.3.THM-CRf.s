%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:58 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  175 (1908 expanded)
%              Number of clauses        :  109 ( 694 expanded)
%              Number of leaves         :   17 ( 423 expanded)
%              Depth                    :   29
%              Number of atoms          :  550 (8524 expanded)
%              Number of equality atoms :  252 (1931 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ r2_hidden(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ r2_hidden(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f25,f40,f39])).

fof(f68,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK2(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f53])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1044,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1024,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1027,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4097,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1027])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1037,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1618,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1024,c_1037])).

cnf(c_4101,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4097,c_1618])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4664,plain,
    ( sK4 = k1_xboole_0
    | k1_relat_1(sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4101,c_30])).

cnf(c_4665,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4664])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1042,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4669,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4665,c_1042])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1467,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1047])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_201,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_266,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_201])).

cnf(c_1021,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_2482,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_1021])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1046,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2630,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2482,c_1046])).

cnf(c_4887,plain,
    ( r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4669,c_2630])).

cnf(c_4888,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4887])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1036,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1714,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1024,c_1036])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1025,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1799,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1714,c_1025])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1043,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1040,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3052,plain,
    ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
    | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_1040])).

cnf(c_7238,plain,
    ( k1_funct_1(sK6,sK0(sK7,sK5,sK6)) = sK7
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_3052])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7871,plain,
    ( k1_funct_1(sK6,sK0(sK7,sK5,sK6)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7238,c_29,c_2630])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1026,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7937,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),sK3) != iProver_top
    | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7871,c_1026])).

cnf(c_7955,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4888,c_7937])).

cnf(c_8030,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7955,c_1799])).

cnf(c_8031,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_8030])).

cnf(c_8036,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_8031])).

cnf(c_8039,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8036,c_1799,c_2630])).

cnf(c_8049,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8039,c_1024])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1031,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8286,plain,
    ( sK3 = k1_xboole_0
    | sK6 = k1_xboole_0
    | v1_funct_2(sK6,sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8049,c_1031])).

cnf(c_1023,plain,
    ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8050,plain,
    ( v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8039,c_1023])).

cnf(c_8867,plain,
    ( sK6 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8286,c_8050])).

cnf(c_8868,plain,
    ( sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8867])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | k1_relset_1(X0,X2,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1033,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | r2_hidden(sK2(X0,X2),X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2242,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | r2_hidden(sK2(sK3,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1033])).

cnf(c_2245,plain,
    ( k1_relat_1(sK6) = sK3
    | r2_hidden(sK2(sK3,sK6),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2242,c_1618])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1038,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2358,plain,
    ( k1_relat_1(sK6) = sK3
    | r1_tarski(sK3,sK2(sK3,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2245,c_1038])).

cnf(c_8876,plain,
    ( k1_relat_1(sK6) = sK3
    | sK6 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2(k1_xboole_0,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8868,c_2358])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1049,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11102,plain,
    ( k1_relat_1(sK6) = sK3
    | sK6 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8876,c_1049])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK1(X2,X0)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | k1_relset_1(X1,X3,X2) != X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1035,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4067,plain,
    ( k1_relat_1(sK6) != sK3
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_1035])).

cnf(c_31,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4529,plain,
    ( r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | k1_relat_1(sK6) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4067,c_31])).

cnf(c_4530,plain,
    ( k1_relat_1(sK6) != sK3
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_4529])).

cnf(c_11107,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_11102,c_4530])).

cnf(c_8789,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),sK5)
    | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8790,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),sK5) = iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8789])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1041,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7936,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK7,sK5,sK6),sK7),sK6) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7871,c_1041])).

cnf(c_8788,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6))
    | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8792,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8788])).

cnf(c_10398,plain,
    ( r2_hidden(k4_tarski(sK0(sK7,sK5,sK6),sK7),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7936,c_29,c_1799,c_2630,c_8792])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1039,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10405,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10398,c_1039])).

cnf(c_10825,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10405,c_1799,c_2630,c_8792])).

cnf(c_11106,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK0(sK7,sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11102,c_10825])).

cnf(c_11246,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11107,c_1799,c_2630,c_7937,c_8790,c_11106])).

cnf(c_11272,plain,
    ( r2_hidden(sK7,k9_relat_1(k1_xboole_0,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11246,c_1799])).

cnf(c_3043,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(X1,k4_tarski(sK0(X0,X2,X1),X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_1038])).

cnf(c_3968,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_3043])).

cnf(c_93,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_95,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_1435,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_1436,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1435])).

cnf(c_1438,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_1530,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1531,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1530])).

cnf(c_1533,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_5266,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3968,c_95,c_1438,c_1533])).

cnf(c_11764,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11272,c_5266])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:40:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.77/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/1.00  
% 3.77/1.00  ------  iProver source info
% 3.77/1.00  
% 3.77/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.77/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/1.00  git: non_committed_changes: false
% 3.77/1.00  git: last_make_outside_of_git: false
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  ------ Parsing...
% 3.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/1.00  ------ Proving...
% 3.77/1.00  ------ Problem Properties 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  clauses                                 29
% 3.77/1.00  conjectures                             5
% 3.77/1.00  EPR                                     5
% 3.77/1.00  Horn                                    24
% 3.77/1.00  unary                                   6
% 3.77/1.00  binary                                  5
% 3.77/1.00  lits                                    79
% 3.77/1.00  lits eq                                 16
% 3.77/1.00  fd_pure                                 0
% 3.77/1.00  fd_pseudo                               0
% 3.77/1.00  fd_cond                                 3
% 3.77/1.00  fd_pseudo_cond                          1
% 3.77/1.00  AC symbols                              0
% 3.77/1.00  
% 3.77/1.00  ------ Input Options Time Limit: Unbounded
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  Current options:
% 3.77/1.00  ------ 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ Proving...
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS status Theorem for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00   Resolution empty clause
% 3.77/1.00  
% 3.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  fof(f5,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f15,plain,(
% 3.77/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.77/1.00    inference(ennf_transformation,[],[f5])).
% 3.77/1.00  
% 3.77/1.00  fof(f27,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.77/1.00    inference(nnf_transformation,[],[f15])).
% 3.77/1.00  
% 3.77/1.00  fof(f28,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.77/1.00    inference(rectify,[],[f27])).
% 3.77/1.00  
% 3.77/1.00  fof(f29,plain,(
% 3.77/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f30,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.77/1.00  
% 3.77/1.00  fof(f49,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f30])).
% 3.77/1.00  
% 3.77/1.00  fof(f12,conjecture,(
% 3.77/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f13,negated_conjecture,(
% 3.77/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.77/1.00    inference(negated_conjecture,[],[f12])).
% 3.77/1.00  
% 3.77/1.00  fof(f24,plain,(
% 3.77/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.77/1.00    inference(ennf_transformation,[],[f13])).
% 3.77/1.00  
% 3.77/1.00  fof(f25,plain,(
% 3.77/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.77/1.00    inference(flattening,[],[f24])).
% 3.77/1.00  
% 3.77/1.00  fof(f40,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f39,plain,(
% 3.77/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f41,plain,(
% 3.77/1.00    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f25,f40,f39])).
% 3.77/1.00  
% 3.77/1.00  fof(f68,plain,(
% 3.77/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.77/1.00    inference(cnf_transformation,[],[f41])).
% 3.77/1.00  
% 3.77/1.00  fof(f11,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f22,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.00    inference(ennf_transformation,[],[f11])).
% 3.77/1.00  
% 3.77/1.00  fof(f23,plain,(
% 3.77/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.00    inference(flattening,[],[f22])).
% 3.77/1.00  
% 3.77/1.00  fof(f38,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.00    inference(nnf_transformation,[],[f23])).
% 3.77/1.00  
% 3.77/1.00  fof(f60,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f38])).
% 3.77/1.00  
% 3.77/1.00  fof(f8,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f19,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.00    inference(ennf_transformation,[],[f8])).
% 3.77/1.00  
% 3.77/1.00  fof(f55,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f19])).
% 3.77/1.00  
% 3.77/1.00  fof(f67,plain,(
% 3.77/1.00    v1_funct_2(sK6,sK3,sK4)),
% 3.77/1.00    inference(cnf_transformation,[],[f41])).
% 3.77/1.00  
% 3.77/1.00  fof(f47,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f30])).
% 3.77/1.00  
% 3.77/1.00  fof(f2,axiom,(
% 3.77/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f26,plain,(
% 3.77/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.77/1.00    inference(nnf_transformation,[],[f2])).
% 3.77/1.00  
% 3.77/1.00  fof(f43,plain,(
% 3.77/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f26])).
% 3.77/1.00  
% 3.77/1.00  fof(f3,axiom,(
% 3.77/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f14,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f3])).
% 3.77/1.00  
% 3.77/1.00  fof(f45,plain,(
% 3.77/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f14])).
% 3.77/1.00  
% 3.77/1.00  fof(f44,plain,(
% 3.77/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f26])).
% 3.77/1.00  
% 3.77/1.00  fof(f4,axiom,(
% 3.77/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f46,plain,(
% 3.77/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f4])).
% 3.77/1.00  
% 3.77/1.00  fof(f9,axiom,(
% 3.77/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f20,plain,(
% 3.77/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/1.00    inference(ennf_transformation,[],[f9])).
% 3.77/1.00  
% 3.77/1.00  fof(f56,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f20])).
% 3.77/1.00  
% 3.77/1.00  fof(f69,plain,(
% 3.77/1.00    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 3.77/1.00    inference(cnf_transformation,[],[f41])).
% 3.77/1.00  
% 3.77/1.00  fof(f48,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f30])).
% 3.77/1.00  
% 3.77/1.00  fof(f6,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f16,plain,(
% 3.77/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.77/1.00    inference(ennf_transformation,[],[f6])).
% 3.77/1.00  
% 3.77/1.00  fof(f17,plain,(
% 3.77/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.77/1.00    inference(flattening,[],[f16])).
% 3.77/1.00  
% 3.77/1.00  fof(f31,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.77/1.00    inference(nnf_transformation,[],[f17])).
% 3.77/1.00  
% 3.77/1.00  fof(f32,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.77/1.00    inference(flattening,[],[f31])).
% 3.77/1.00  
% 3.77/1.00  fof(f52,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f32])).
% 3.77/1.00  
% 3.77/1.00  fof(f66,plain,(
% 3.77/1.00    v1_funct_1(sK6)),
% 3.77/1.00    inference(cnf_transformation,[],[f41])).
% 3.77/1.00  
% 3.77/1.00  fof(f70,plain,(
% 3.77/1.00    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f41])).
% 3.77/1.00  
% 3.77/1.00  fof(f64,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f38])).
% 3.77/1.00  
% 3.77/1.00  fof(f74,plain,(
% 3.77/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.77/1.00    inference(equality_resolution,[],[f64])).
% 3.77/1.00  
% 3.77/1.00  fof(f10,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f21,plain,(
% 3.77/1.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.77/1.00    inference(ennf_transformation,[],[f10])).
% 3.77/1.00  
% 3.77/1.00  fof(f33,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.77/1.00    inference(nnf_transformation,[],[f21])).
% 3.77/1.00  
% 3.77/1.00  fof(f34,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.77/1.00    inference(rectify,[],[f33])).
% 3.77/1.00  
% 3.77/1.00  fof(f36,plain,(
% 3.77/1.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f35,plain,(
% 3.77/1.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f37,plain,(
% 3.77/1.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).
% 3.77/1.00  
% 3.77/1.00  fof(f57,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK2(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f37])).
% 3.77/1.00  
% 3.77/1.00  fof(f7,axiom,(
% 3.77/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f18,plain,(
% 3.77/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.77/1.00    inference(ennf_transformation,[],[f7])).
% 3.77/1.00  
% 3.77/1.00  fof(f54,plain,(
% 3.77/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f18])).
% 3.77/1.00  
% 3.77/1.00  fof(f1,axiom,(
% 3.77/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f42,plain,(
% 3.77/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f1])).
% 3.77/1.00  
% 3.77/1.00  fof(f59,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.77/1.00    inference(cnf_transformation,[],[f37])).
% 3.77/1.00  
% 3.77/1.00  fof(f53,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f32])).
% 3.77/1.00  
% 3.77/1.00  fof(f71,plain,(
% 3.77/1.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.77/1.00    inference(equality_resolution,[],[f53])).
% 3.77/1.00  
% 3.77/1.00  fof(f51,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f32])).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.77/1.00      | r2_hidden(sK0(X0,X2,X1),X2)
% 3.77/1.00      | ~ v1_relat_1(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1044,plain,
% 3.77/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.77/1.00      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_26,negated_conjecture,
% 3.77/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.77/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1024,plain,
% 3.77/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_23,plain,
% 3.77/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.77/1.00      | k1_xboole_0 = X2 ),
% 3.77/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1027,plain,
% 3.77/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.77/1.00      | k1_xboole_0 = X1
% 3.77/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4097,plain,
% 3.77/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 3.77/1.00      | sK4 = k1_xboole_0
% 3.77/1.00      | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1024,c_1027]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_13,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1037,plain,
% 3.77/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1618,plain,
% 3.77/1.00      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1024,c_1037]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4101,plain,
% 3.77/1.00      ( k1_relat_1(sK6) = sK3
% 3.77/1.00      | sK4 = k1_xboole_0
% 3.77/1.00      | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_4097,c_1618]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_27,negated_conjecture,
% 3.77/1.00      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.77/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_30,plain,
% 3.77/1.00      ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4664,plain,
% 3.77/1.00      ( sK4 = k1_xboole_0 | k1_relat_1(sK6) = sK3 ),
% 3.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4101,c_30]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4665,plain,
% 3.77/1.00      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_4664]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.77/1.00      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 3.77/1.00      | ~ v1_relat_1(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1042,plain,
% 3.77/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.77/1.00      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4669,plain,
% 3.77/1.00      ( sK4 = k1_xboole_0
% 3.77/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.77/1.00      | r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_4665,c_1042]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1047,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.77/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1467,plain,
% 3.77/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1024,c_1047]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_200,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.77/1.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_201,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_200]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_266,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.77/1.00      inference(bin_hyper_res,[status(thm)],[c_3,c_201]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1021,plain,
% 3.77/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top
% 3.77/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2482,plain,
% 3.77/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1467,c_1021]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4,plain,
% 3.77/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1046,plain,
% 3.77/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2630,plain,
% 3.77/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.77/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2482,c_1046]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4887,plain,
% 3.77/1.00      ( r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top
% 3.77/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.77/1.00      | sK4 = k1_xboole_0 ),
% 3.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4669,c_2630]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4888,plain,
% 3.77/1.00      ( sK4 = k1_xboole_0
% 3.77/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.77/1.00      | r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_4887]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_14,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.77/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1036,plain,
% 3.77/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1714,plain,
% 3.77/1.00      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1024,c_1036]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_25,negated_conjecture,
% 3.77/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1025,plain,
% 3.77/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1799,plain,
% 3.77/1.00      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_1714,c_1025]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.77/1.00      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.77/1.00      | ~ v1_relat_1(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1043,plain,
% 3.77/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.77/1.00      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_10,plain,
% 3.77/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.77/1.00      | ~ v1_funct_1(X2)
% 3.77/1.00      | ~ v1_relat_1(X2)
% 3.77/1.00      | k1_funct_1(X2,X0) = X1 ),
% 3.77/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1040,plain,
% 3.77/1.00      ( k1_funct_1(X0,X1) = X2
% 3.77/1.00      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.77/1.00      | v1_funct_1(X0) != iProver_top
% 3.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3052,plain,
% 3.77/1.00      ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
% 3.77/1.00      | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
% 3.77/1.00      | v1_funct_1(X0) != iProver_top
% 3.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1043,c_1040]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7238,plain,
% 3.77/1.00      ( k1_funct_1(sK6,sK0(sK7,sK5,sK6)) = sK7
% 3.77/1.00      | v1_funct_1(sK6) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1799,c_3052]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_28,negated_conjecture,
% 3.77/1.00      ( v1_funct_1(sK6) ),
% 3.77/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_29,plain,
% 3.77/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7871,plain,
% 3.77/1.00      ( k1_funct_1(sK6,sK0(sK7,sK5,sK6)) = sK7 ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_7238,c_29,c_2630]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_24,negated_conjecture,
% 3.77/1.00      ( ~ r2_hidden(X0,sK3) | ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,X0) != sK7 ),
% 3.77/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1026,plain,
% 3.77/1.00      ( k1_funct_1(sK6,X0) != sK7
% 3.77/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.77/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7937,plain,
% 3.77/1.00      ( r2_hidden(sK0(sK7,sK5,sK6),sK3) != iProver_top
% 3.77/1.00      | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_7871,c_1026]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7955,plain,
% 3.77/1.00      ( sK4 = k1_xboole_0
% 3.77/1.00      | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
% 3.77/1.00      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_4888,c_7937]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8030,plain,
% 3.77/1.00      ( r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top | sK4 = k1_xboole_0 ),
% 3.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7955,c_1799]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8031,plain,
% 3.77/1.00      ( sK4 = k1_xboole_0 | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_8030]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8036,plain,
% 3.77/1.00      ( sK4 = k1_xboole_0
% 3.77/1.00      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1044,c_8031]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8039,plain,
% 3.77/1.00      ( sK4 = k1_xboole_0 ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_8036,c_1799,c_2630]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8049,plain,
% 3.77/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_8039,c_1024]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_19,plain,
% 3.77/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.77/1.00      | k1_xboole_0 = X1
% 3.77/1.00      | k1_xboole_0 = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1031,plain,
% 3.77/1.00      ( k1_xboole_0 = X0
% 3.77/1.00      | k1_xboole_0 = X1
% 3.77/1.00      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.77/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8286,plain,
% 3.77/1.00      ( sK3 = k1_xboole_0
% 3.77/1.00      | sK6 = k1_xboole_0
% 3.77/1.00      | v1_funct_2(sK6,sK3,k1_xboole_0) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_8049,c_1031]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1023,plain,
% 3.77/1.00      ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8050,plain,
% 3.77/1.00      ( v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_8039,c_1023]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8867,plain,
% 3.77/1.00      ( sK6 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8286,c_8050]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8868,plain,
% 3.77/1.00      ( sK3 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_8867]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_17,plain,
% 3.77/1.00      ( r2_hidden(sK2(X0,X1),X0)
% 3.77/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 3.77/1.00      | k1_relset_1(X0,X2,X1) = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1033,plain,
% 3.77/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.77/1.00      | r2_hidden(sK2(X0,X2),X0) = iProver_top
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2242,plain,
% 3.77/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 3.77/1.00      | r2_hidden(sK2(sK3,sK6),sK3) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1024,c_1033]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2245,plain,
% 3.77/1.00      ( k1_relat_1(sK6) = sK3 | r2_hidden(sK2(sK3,sK6),sK3) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_2242,c_1618]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_12,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1038,plain,
% 3.77/1.00      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2358,plain,
% 3.77/1.00      ( k1_relat_1(sK6) = sK3 | r1_tarski(sK3,sK2(sK3,sK6)) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2245,c_1038]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8876,plain,
% 3.77/1.00      ( k1_relat_1(sK6) = sK3
% 3.77/1.00      | sK6 = k1_xboole_0
% 3.77/1.00      | r1_tarski(k1_xboole_0,sK2(k1_xboole_0,sK6)) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_8868,c_2358]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_0,plain,
% 3.77/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1049,plain,
% 3.77/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11102,plain,
% 3.77/1.00      ( k1_relat_1(sK6) = sK3 | sK6 = k1_xboole_0 ),
% 3.77/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_8876,c_1049]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_15,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,X1)
% 3.77/1.00      | r2_hidden(k4_tarski(X0,sK1(X2,X0)),X2)
% 3.77/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.77/1.00      | k1_relset_1(X1,X3,X2) != X1 ),
% 3.77/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1035,plain,
% 3.77/1.00      ( k1_relset_1(X0,X1,X2) != X0
% 3.77/1.00      | r2_hidden(X3,X0) != iProver_top
% 3.77/1.00      | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4067,plain,
% 3.77/1.00      ( k1_relat_1(sK6) != sK3
% 3.77/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.77/1.00      | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top
% 3.77/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1618,c_1035]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_31,plain,
% 3.77/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4529,plain,
% 3.77/1.00      ( r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top
% 3.77/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.77/1.00      | k1_relat_1(sK6) != sK3 ),
% 3.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4067,c_31]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4530,plain,
% 3.77/1.00      ( k1_relat_1(sK6) != sK3
% 3.77/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.77/1.00      | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_4529]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11107,plain,
% 3.77/1.00      ( sK6 = k1_xboole_0
% 3.77/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.77/1.00      | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_11102,c_4530]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8789,plain,
% 3.77/1.00      ( r2_hidden(sK0(sK7,sK5,sK6),sK5)
% 3.77/1.00      | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
% 3.77/1.00      | ~ v1_relat_1(sK6) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8790,plain,
% 3.77/1.00      ( r2_hidden(sK0(sK7,sK5,sK6),sK5) = iProver_top
% 3.77/1.00      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_8789]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.77/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.77/1.00      | ~ v1_funct_1(X1)
% 3.77/1.00      | ~ v1_relat_1(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1041,plain,
% 3.77/1.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.77/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 3.77/1.00      | v1_funct_1(X1) != iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7936,plain,
% 3.77/1.00      ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
% 3.77/1.00      | r2_hidden(k4_tarski(sK0(sK7,sK5,sK6),sK7),sK6) = iProver_top
% 3.77/1.00      | v1_funct_1(sK6) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_7871,c_1041]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8788,plain,
% 3.77/1.00      ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6))
% 3.77/1.00      | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
% 3.77/1.00      | ~ v1_relat_1(sK6) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8792,plain,
% 3.77/1.00      ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6)) = iProver_top
% 3.77/1.00      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_8788]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_10398,plain,
% 3.77/1.00      ( r2_hidden(k4_tarski(sK0(sK7,sK5,sK6),sK7),sK6) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_7936,c_29,c_1799,c_2630,c_8792]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11,plain,
% 3.77/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.77/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.77/1.00      | ~ v1_funct_1(X1)
% 3.77/1.00      | ~ v1_relat_1(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1039,plain,
% 3.77/1.00      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.77/1.00      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 3.77/1.00      | v1_funct_1(X1) != iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_10405,plain,
% 3.77/1.00      ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6)) = iProver_top
% 3.77/1.00      | v1_funct_1(sK6) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_10398,c_1039]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_10825,plain,
% 3.77/1.00      ( r2_hidden(sK0(sK7,sK5,sK6),k1_relat_1(sK6)) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_10405,c_1799,c_2630,c_8792]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11106,plain,
% 3.77/1.00      ( sK6 = k1_xboole_0 | r2_hidden(sK0(sK7,sK5,sK6),sK3) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_11102,c_10825]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11246,plain,
% 3.77/1.00      ( sK6 = k1_xboole_0 ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_11107,c_1799,c_2630,c_7937,c_8790,c_11106]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11272,plain,
% 3.77/1.00      ( r2_hidden(sK7,k9_relat_1(k1_xboole_0,sK5)) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_11246,c_1799]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3043,plain,
% 3.77/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.77/1.00      | r1_tarski(X1,k4_tarski(sK0(X0,X2,X1),X0)) != iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1043,c_1038]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3968,plain,
% 3.77/1.00      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
% 3.77/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1049,c_3043]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_93,plain,
% 3.77/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_95,plain,
% 3.77/1.00      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_93]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1435,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.77/1.00      | v1_relat_1(X0)
% 3.77/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_266]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1436,plain,
% 3.77/1.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.77/1.00      | v1_relat_1(X0) = iProver_top
% 3.77/1.00      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1435]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1438,plain,
% 3.77/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.77/1.00      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.77/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_1436]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1530,plain,
% 3.77/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1531,plain,
% 3.77/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1530]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1533,plain,
% 3.77/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_1531]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5266,plain,
% 3.77/1.00      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_3968,c_95,c_1438,c_1533]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11764,plain,
% 3.77/1.00      ( $false ),
% 3.77/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_11272,c_5266]) ).
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  ------                               Statistics
% 3.77/1.00  
% 3.77/1.00  ------ Selected
% 3.77/1.00  
% 3.77/1.00  total_time:                             0.453
% 3.77/1.00  
%------------------------------------------------------------------------------

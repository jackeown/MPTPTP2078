%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:56 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  158 (2828 expanded)
%              Number of clauses        :   95 ( 901 expanded)
%              Number of leaves         :   21 ( 718 expanded)
%              Depth                    :   27
%              Number of atoms          :  589 (15352 expanded)
%              Number of equality atoms :  261 (4045 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
        & r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
              ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK2(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2)
                  & r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
                    & r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).

fof(f57,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ r2_hidden(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f23,f41,f40])).

fof(f74,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f72,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f76,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ r2_hidden(X5,sK5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_884,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_872,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_875,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1392,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_872,c_875])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1393,plain,
    ( ~ v1_funct_2(sK8,sK5,sK6)
    | k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1392])).

cnf(c_1802,plain,
    ( sK6 = k1_xboole_0
    | k1_relset_1(sK5,sK6,sK8) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1392,c_32,c_1393])).

cnf(c_1803,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1802])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_882,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1498,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_872,c_882])).

cnf(c_1804,plain,
    ( k1_relat_1(sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1803,c_1498])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_883,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4157,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_883])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1522,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_7,c_31])).

cnf(c_1523,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1592,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1593,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1592])).

cnf(c_5331,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4157,c_34,c_1523,c_1593])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_881,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2155,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_872,c_881])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_873,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2538,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2155,c_873])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_885,plain,
    ( k1_funct_1(X0,sK4(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4409,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2538,c_885])).

cnf(c_5016,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4409,c_34,c_1523,c_1593])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_874,plain,
    ( k1_funct_1(sK8,X0) != sK9
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5020,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5016,c_874])).

cnf(c_5343,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5331,c_5020])).

cnf(c_5575,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5343,c_2538])).

cnf(c_5576,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5575])).

cnf(c_5581,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_5576])).

cnf(c_5584,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5581,c_34,c_1523,c_1593,c_2538])).

cnf(c_5591,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5584,c_872])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_879,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6421,plain,
    ( sK5 = k1_xboole_0
    | sK8 = k1_xboole_0
    | v1_funct_2(sK8,sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5591,c_879])).

cnf(c_35,plain,
    ( v1_funct_2(sK8,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_317,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_344,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_1481,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_330,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1349,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK8,sK5,sK6)
    | X2 != sK6
    | X1 != sK5
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_1480,plain,
    ( v1_funct_2(sK8,X0,X1)
    | ~ v1_funct_2(sK8,sK5,sK6)
    | X1 != sK6
    | X0 != sK5
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_1769,plain,
    ( v1_funct_2(sK8,sK5,X0)
    | ~ v1_funct_2(sK8,sK5,sK6)
    | X0 != sK6
    | sK5 != sK5
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_1771,plain,
    ( X0 != sK6
    | sK5 != sK5
    | sK8 != sK8
    | v1_funct_2(sK8,sK5,X0) = iProver_top
    | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(c_1773,plain,
    ( sK5 != sK5
    | sK8 != sK8
    | k1_xboole_0 != sK6
    | v1_funct_2(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_1770,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_318,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2376,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_2377,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2376])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_892,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_901,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3472,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_901])).

cnf(c_3849,plain,
    ( v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2538,c_3472])).

cnf(c_3879,plain,
    ( ~ v1_relat_1(sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3849])).

cnf(c_319,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5509,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_5511,plain,
    ( v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5509])).

cnf(c_6735,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6421,c_34,c_35,c_2,c_344,c_1481,c_1522,c_1523,c_1592,c_1593,c_1773,c_1770,c_2377,c_2538,c_3879,c_5511,c_5581])).

cnf(c_5590,plain,
    ( k1_relset_1(sK5,k1_xboole_0,sK8) = k1_relat_1(sK8) ),
    inference(demodulation,[status(thm)],[c_5584,c_1498])).

cnf(c_6740,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_relat_1(sK8) ),
    inference(demodulation,[status(thm)],[c_6735,c_5590])).

cnf(c_6741,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6735,c_5591])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_876,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7008,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6741,c_876])).

cnf(c_1482,plain,
    ( X0 != sK6
    | X1 != sK5
    | sK8 != sK8
    | v1_funct_2(sK8,X1,X0) = iProver_top
    | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_1484,plain,
    ( sK8 != sK8
    | k1_xboole_0 != sK6
    | k1_xboole_0 != sK5
    | v1_funct_2(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_1775,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_1776,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_7236,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7008,c_34,c_35,c_2,c_344,c_1484,c_1481,c_1522,c_1523,c_1592,c_1593,c_1773,c_1770,c_1776,c_2377,c_2538,c_3879,c_5511,c_5581,c_6421])).

cnf(c_7634,plain,
    ( k1_relat_1(sK8) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6740,c_7236])).

cnf(c_5491,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK8))
    | k1_relat_1(sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_5493,plain,
    ( v1_xboole_0(k1_relat_1(sK8))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK8) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5491])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_891,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3288,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(k1_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_891,c_901])).

cnf(c_4115,plain,
    ( v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2538,c_3288])).

cnf(c_4151,plain,
    ( ~ v1_relat_1(sK8)
    | ~ v1_xboole_0(k1_relat_1(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4115])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7634,c_5493,c_4151,c_1592,c_1522,c_2])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:30:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.74/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/0.99  
% 3.74/0.99  ------  iProver source info
% 3.74/0.99  
% 3.74/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.74/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/0.99  git: non_committed_changes: false
% 3.74/0.99  git: last_make_outside_of_git: false
% 3.74/0.99  
% 3.74/0.99  ------ 
% 3.74/0.99  ------ Parsing...
% 3.74/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/0.99  
% 3.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.99  ------ Proving...
% 3.74/0.99  ------ Problem Properties 
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  clauses                                 34
% 3.74/0.99  conjectures                             5
% 3.74/0.99  EPR                                     8
% 3.74/0.99  Horn                                    25
% 3.74/0.99  unary                                   6
% 3.74/0.99  binary                                  5
% 3.74/0.99  lits                                    105
% 3.74/0.99  lits eq                                 19
% 3.74/0.99  fd_pure                                 0
% 3.74/0.99  fd_pseudo                               0
% 3.74/0.99  fd_cond                                 3
% 3.74/0.99  fd_pseudo_cond                          4
% 3.74/0.99  AC symbols                              0
% 3.74/0.99  
% 3.74/0.99  ------ Input Options Time Limit: Unbounded
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ 
% 3.74/0.99  Current options:
% 3.74/0.99  ------ 
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  ------ Proving...
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS status Theorem for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  fof(f7,axiom,(
% 3.74/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f16,plain,(
% 3.74/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.74/0.99    inference(ennf_transformation,[],[f7])).
% 3.74/0.99  
% 3.74/0.99  fof(f17,plain,(
% 3.74/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.74/0.99    inference(flattening,[],[f16])).
% 3.74/0.99  
% 3.74/0.99  fof(f33,plain,(
% 3.74/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.74/0.99    inference(nnf_transformation,[],[f17])).
% 3.74/0.99  
% 3.74/0.99  fof(f34,plain,(
% 3.74/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.74/0.99    inference(rectify,[],[f33])).
% 3.74/0.99  
% 3.74/0.99  fof(f37,plain,(
% 3.74/0.99    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f36,plain,(
% 3.74/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f35,plain,(
% 3.74/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK2(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f38,plain,(
% 3.74/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).
% 3.74/0.99  
% 3.74/0.99  fof(f57,plain,(
% 3.74/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f38])).
% 3.74/0.99  
% 3.74/0.99  fof(f80,plain,(
% 3.74/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(equality_resolution,[],[f57])).
% 3.74/0.99  
% 3.74/0.99  fof(f11,conjecture,(
% 3.74/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f12,negated_conjecture,(
% 3.74/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.74/0.99    inference(negated_conjecture,[],[f11])).
% 3.74/0.99  
% 3.74/0.99  fof(f22,plain,(
% 3.74/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.74/0.99    inference(ennf_transformation,[],[f12])).
% 3.74/0.99  
% 3.74/0.99  fof(f23,plain,(
% 3.74/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.74/0.99    inference(flattening,[],[f22])).
% 3.74/0.99  
% 3.74/0.99  fof(f41,plain,(
% 3.74/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f40,plain,(
% 3.74/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f42,plain,(
% 3.74/0.99    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f23,f41,f40])).
% 3.74/0.99  
% 3.74/0.99  fof(f74,plain,(
% 3.74/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f10,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f20,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/0.99    inference(ennf_transformation,[],[f10])).
% 3.74/0.99  
% 3.74/0.99  fof(f21,plain,(
% 3.74/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/0.99    inference(flattening,[],[f20])).
% 3.74/0.99  
% 3.74/0.99  fof(f39,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/0.99    inference(nnf_transformation,[],[f21])).
% 3.74/0.99  
% 3.74/0.99  fof(f66,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f39])).
% 3.74/0.99  
% 3.74/0.99  fof(f73,plain,(
% 3.74/0.99    v1_funct_2(sK8,sK5,sK6)),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f8,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f18,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/0.99    inference(ennf_transformation,[],[f8])).
% 3.74/0.99  
% 3.74/0.99  fof(f64,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f18])).
% 3.74/0.99  
% 3.74/0.99  fof(f56,plain,(
% 3.74/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f38])).
% 3.74/0.99  
% 3.74/0.99  fof(f81,plain,(
% 3.74/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(equality_resolution,[],[f56])).
% 3.74/0.99  
% 3.74/0.99  fof(f72,plain,(
% 3.74/0.99    v1_funct_1(sK8)),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f4,axiom,(
% 3.74/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f14,plain,(
% 3.74/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.74/0.99    inference(ennf_transformation,[],[f4])).
% 3.74/0.99  
% 3.74/0.99  fof(f50,plain,(
% 3.74/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f14])).
% 3.74/0.99  
% 3.74/0.99  fof(f5,axiom,(
% 3.74/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f51,plain,(
% 3.74/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f5])).
% 3.74/0.99  
% 3.74/0.99  fof(f9,axiom,(
% 3.74/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f19,plain,(
% 3.74/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/0.99    inference(ennf_transformation,[],[f9])).
% 3.74/0.99  
% 3.74/0.99  fof(f65,plain,(
% 3.74/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f19])).
% 3.74/0.99  
% 3.74/0.99  fof(f75,plain,(
% 3.74/0.99    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f58,plain,(
% 3.74/0.99    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f38])).
% 3.74/0.99  
% 3.74/0.99  fof(f79,plain,(
% 3.74/0.99    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/0.99    inference(equality_resolution,[],[f58])).
% 3.74/0.99  
% 3.74/0.99  fof(f76,plain,(
% 3.74/0.99    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~r2_hidden(X5,sK5)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f42])).
% 3.74/0.99  
% 3.74/0.99  fof(f70,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f39])).
% 3.74/0.99  
% 3.74/0.99  fof(f84,plain,(
% 3.74/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.74/0.99    inference(equality_resolution,[],[f70])).
% 3.74/0.99  
% 3.74/0.99  fof(f2,axiom,(
% 3.74/0.99    v1_xboole_0(k1_xboole_0)),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f45,plain,(
% 3.74/0.99    v1_xboole_0(k1_xboole_0)),
% 3.74/0.99    inference(cnf_transformation,[],[f2])).
% 3.74/0.99  
% 3.74/0.99  fof(f6,axiom,(
% 3.74/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f15,plain,(
% 3.74/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.74/0.99    inference(ennf_transformation,[],[f6])).
% 3.74/0.99  
% 3.74/0.99  fof(f29,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.74/0.99    inference(nnf_transformation,[],[f15])).
% 3.74/0.99  
% 3.74/0.99  fof(f30,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.74/0.99    inference(rectify,[],[f29])).
% 3.74/0.99  
% 3.74/0.99  fof(f31,plain,(
% 3.74/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f32,plain,(
% 3.74/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.74/0.99  
% 3.74/0.99  fof(f53,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f32])).
% 3.74/0.99  
% 3.74/0.99  fof(f1,axiom,(
% 3.74/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.99  
% 3.74/0.99  fof(f24,plain,(
% 3.74/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.74/0.99    inference(nnf_transformation,[],[f1])).
% 3.74/0.99  
% 3.74/0.99  fof(f25,plain,(
% 3.74/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.74/0.99    inference(rectify,[],[f24])).
% 3.74/0.99  
% 3.74/0.99  fof(f26,plain,(
% 3.74/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.74/0.99    introduced(choice_axiom,[])).
% 3.74/0.99  
% 3.74/0.99  fof(f27,plain,(
% 3.74/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.74/0.99  
% 3.74/0.99  fof(f43,plain,(
% 3.74/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f27])).
% 3.74/0.99  
% 3.74/0.99  fof(f67,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/0.99    inference(cnf_transformation,[],[f39])).
% 3.74/0.99  
% 3.74/0.99  fof(f86,plain,(
% 3.74/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.74/0.99    inference(equality_resolution,[],[f67])).
% 3.74/0.99  
% 3.74/0.99  fof(f52,plain,(
% 3.74/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.74/0.99    inference(cnf_transformation,[],[f32])).
% 3.74/0.99  
% 3.74/0.99  cnf(c_19,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.74/0.99      | r2_hidden(sK4(X1,X2,X0),X2)
% 3.74/0.99      | ~ v1_funct_1(X1)
% 3.74/0.99      | ~ v1_relat_1(X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_884,plain,
% 3.74/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.74/0.99      | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
% 3.74/0.99      | v1_funct_1(X1) != iProver_top
% 3.74/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_31,negated_conjecture,
% 3.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.74/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_872,plain,
% 3.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_28,plain,
% 3.74/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.74/0.99      | k1_xboole_0 = X2 ),
% 3.74/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_875,plain,
% 3.74/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.74/0.99      | k1_xboole_0 = X1
% 3.74/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1392,plain,
% 3.74/0.99      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.74/0.99      | sK6 = k1_xboole_0
% 3.74/0.99      | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_872,c_875]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_32,negated_conjecture,
% 3.74/0.99      ( v1_funct_2(sK8,sK5,sK6) ),
% 3.74/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1393,plain,
% 3.74/0.99      ( ~ v1_funct_2(sK8,sK5,sK6)
% 3.74/0.99      | k1_relset_1(sK5,sK6,sK8) = sK5
% 3.74/0.99      | sK6 = k1_xboole_0 ),
% 3.74/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1392]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1802,plain,
% 3.74/0.99      ( sK6 = k1_xboole_0 | k1_relset_1(sK5,sK6,sK8) = sK5 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_1392,c_32,c_1393]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1803,plain,
% 3.74/0.99      ( k1_relset_1(sK5,sK6,sK8) = sK5 | sK6 = k1_xboole_0 ),
% 3.74/0.99      inference(renaming,[status(thm)],[c_1802]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_21,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_882,plain,
% 3.74/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1498,plain,
% 3.74/0.99      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_872,c_882]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1804,plain,
% 3.74/0.99      ( k1_relat_1(sK8) = sK5 | sK6 = k1_xboole_0 ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_1803,c_1498]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_20,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.74/0.99      | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1))
% 3.74/0.99      | ~ v1_funct_1(X1)
% 3.74/0.99      | ~ v1_relat_1(X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_883,plain,
% 3.74/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.74/0.99      | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 3.74/0.99      | v1_funct_1(X1) != iProver_top
% 3.74/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4157,plain,
% 3.74/0.99      ( sK6 = k1_xboole_0
% 3.74/0.99      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.74/0.99      | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top
% 3.74/0.99      | v1_funct_1(sK8) != iProver_top
% 3.74/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_1804,c_883]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_33,negated_conjecture,
% 3.74/0.99      ( v1_funct_1(sK8) ),
% 3.74/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_34,plain,
% 3.74/0.99      ( v1_funct_1(sK8) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.74/0.99      | ~ v1_relat_1(X1)
% 3.74/0.99      | v1_relat_1(X0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1522,plain,
% 3.74/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6)) | v1_relat_1(sK8) ),
% 3.74/0.99      inference(resolution,[status(thm)],[c_7,c_31]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1523,plain,
% 3.74/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.74/0.99      | v1_relat_1(sK8) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_8,plain,
% 3.74/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1592,plain,
% 3.74/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1593,plain,
% 3.74/0.99      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1592]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5331,plain,
% 3.74/0.99      ( sK6 = k1_xboole_0
% 3.74/0.99      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.74/0.99      | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_4157,c_34,c_1523,c_1593]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_22,plain,
% 3.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.74/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_881,plain,
% 3.74/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2155,plain,
% 3.74/0.99      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_872,c_881]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_30,negated_conjecture,
% 3.74/0.99      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.74/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_873,plain,
% 3.74/0.99      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2538,plain,
% 3.74/0.99      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_2155,c_873]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_18,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.74/0.99      | ~ v1_funct_1(X1)
% 3.74/0.99      | ~ v1_relat_1(X1)
% 3.74/0.99      | k1_funct_1(X1,sK4(X1,X2,X0)) = X0 ),
% 3.74/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_885,plain,
% 3.74/0.99      ( k1_funct_1(X0,sK4(X0,X1,X2)) = X2
% 3.74/0.99      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 3.74/0.99      | v1_funct_1(X0) != iProver_top
% 3.74/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4409,plain,
% 3.74/0.99      ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9
% 3.74/0.99      | v1_funct_1(sK8) != iProver_top
% 3.74/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_2538,c_885]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5016,plain,
% 3.74/0.99      ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_4409,c_34,c_1523,c_1593]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_29,negated_conjecture,
% 3.74/0.99      ( ~ r2_hidden(X0,sK5)
% 3.74/0.99      | ~ r2_hidden(X0,sK7)
% 3.74/0.99      | k1_funct_1(sK8,X0) != sK9 ),
% 3.74/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_874,plain,
% 3.74/0.99      ( k1_funct_1(sK8,X0) != sK9
% 3.74/0.99      | r2_hidden(X0,sK5) != iProver_top
% 3.74/0.99      | r2_hidden(X0,sK7) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5020,plain,
% 3.74/0.99      ( r2_hidden(sK4(sK8,sK7,sK9),sK5) != iProver_top
% 3.74/0.99      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_5016,c_874]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5343,plain,
% 3.74/0.99      ( sK6 = k1_xboole_0
% 3.74/0.99      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
% 3.74/0.99      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_5331,c_5020]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5575,plain,
% 3.74/0.99      ( r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
% 3.74/0.99      | sK6 = k1_xboole_0 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_5343,c_2538]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5576,plain,
% 3.74/0.99      ( sK6 = k1_xboole_0
% 3.74/0.99      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
% 3.74/0.99      inference(renaming,[status(thm)],[c_5575]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5581,plain,
% 3.74/0.99      ( sK6 = k1_xboole_0
% 3.74/0.99      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.74/0.99      | v1_funct_1(sK8) != iProver_top
% 3.74/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_884,c_5576]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5584,plain,
% 3.74/0.99      ( sK6 = k1_xboole_0 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_5581,c_34,c_1523,c_1593,c_2538]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5591,plain,
% 3.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_5584,c_872]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_24,plain,
% 3.74/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.74/0.99      | k1_xboole_0 = X1
% 3.74/0.99      | k1_xboole_0 = X0 ),
% 3.74/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_879,plain,
% 3.74/0.99      ( k1_xboole_0 = X0
% 3.74/0.99      | k1_xboole_0 = X1
% 3.74/0.99      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.74/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6421,plain,
% 3.74/0.99      ( sK5 = k1_xboole_0
% 3.74/0.99      | sK8 = k1_xboole_0
% 3.74/0.99      | v1_funct_2(sK8,sK5,k1_xboole_0) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_5591,c_879]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_35,plain,
% 3.74/0.99      ( v1_funct_2(sK8,sK5,sK6) = iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2,plain,
% 3.74/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.74/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_317,plain,( X0 = X0 ),theory(equality) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_344,plain,
% 3.74/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_317]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1481,plain,
% 3.74/0.99      ( sK8 = sK8 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_317]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_330,plain,
% 3.74/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.74/0.99      | v1_funct_2(X3,X4,X5)
% 3.74/0.99      | X3 != X0
% 3.74/0.99      | X4 != X1
% 3.74/0.99      | X5 != X2 ),
% 3.74/0.99      theory(equality) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1349,plain,
% 3.74/0.99      ( v1_funct_2(X0,X1,X2)
% 3.74/0.99      | ~ v1_funct_2(sK8,sK5,sK6)
% 3.74/0.99      | X2 != sK6
% 3.74/0.99      | X1 != sK5
% 3.74/0.99      | X0 != sK8 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_330]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1480,plain,
% 3.74/0.99      ( v1_funct_2(sK8,X0,X1)
% 3.74/0.99      | ~ v1_funct_2(sK8,sK5,sK6)
% 3.74/0.99      | X1 != sK6
% 3.74/0.99      | X0 != sK5
% 3.74/0.99      | sK8 != sK8 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_1349]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1769,plain,
% 3.74/0.99      ( v1_funct_2(sK8,sK5,X0)
% 3.74/0.99      | ~ v1_funct_2(sK8,sK5,sK6)
% 3.74/0.99      | X0 != sK6
% 3.74/0.99      | sK5 != sK5
% 3.74/0.99      | sK8 != sK8 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_1480]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1771,plain,
% 3.74/0.99      ( X0 != sK6
% 3.74/0.99      | sK5 != sK5
% 3.74/0.99      | sK8 != sK8
% 3.74/0.99      | v1_funct_2(sK8,sK5,X0) = iProver_top
% 3.74/0.99      | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1769]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1773,plain,
% 3.74/0.99      ( sK5 != sK5
% 3.74/0.99      | sK8 != sK8
% 3.74/0.99      | k1_xboole_0 != sK6
% 3.74/0.99      | v1_funct_2(sK8,sK5,sK6) != iProver_top
% 3.74/0.99      | v1_funct_2(sK8,sK5,k1_xboole_0) = iProver_top ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_1771]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1770,plain,
% 3.74/0.99      ( sK5 = sK5 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_317]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_318,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2376,plain,
% 3.74/0.99      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_318]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_2377,plain,
% 3.74/0.99      ( sK6 != k1_xboole_0
% 3.74/0.99      | k1_xboole_0 = sK6
% 3.74/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_2376]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_11,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.74/0.99      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.74/0.99      | ~ v1_relat_1(X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_892,plain,
% 3.74/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.74/0.99      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.74/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_901,plain,
% 3.74/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.74/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3472,plain,
% 3.74/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.74/0.99      | v1_relat_1(X1) != iProver_top
% 3.74/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_892,c_901]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3849,plain,
% 3.74/0.99      ( v1_relat_1(sK8) != iProver_top
% 3.74/0.99      | v1_xboole_0(sK8) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_2538,c_3472]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3879,plain,
% 3.74/0.99      ( ~ v1_relat_1(sK8) | ~ v1_xboole_0(sK8) ),
% 3.74/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3849]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_319,plain,
% 3.74/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.74/0.99      theory(equality) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5509,plain,
% 3.74/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK8) | sK8 != X0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_319]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5511,plain,
% 3.74/0.99      ( v1_xboole_0(sK8)
% 3.74/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.74/0.99      | sK8 != k1_xboole_0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_5509]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6735,plain,
% 3.74/0.99      ( sK5 = k1_xboole_0 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_6421,c_34,c_35,c_2,c_344,c_1481,c_1522,c_1523,c_1592,
% 3.74/0.99                 c_1593,c_1773,c_1770,c_2377,c_2538,c_3879,c_5511,c_5581]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5590,plain,
% 3.74/0.99      ( k1_relset_1(sK5,k1_xboole_0,sK8) = k1_relat_1(sK8) ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_5584,c_1498]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6740,plain,
% 3.74/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_relat_1(sK8) ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_6735,c_5590]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_6741,plain,
% 3.74/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.74/0.99      inference(demodulation,[status(thm)],[c_6735,c_5591]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_27,plain,
% 3.74/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.74/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.74/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_876,plain,
% 3.74/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.74/0.99      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 3.74/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7008,plain,
% 3.74/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
% 3.74/0.99      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_6741,c_876]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1482,plain,
% 3.74/0.99      ( X0 != sK6
% 3.74/0.99      | X1 != sK5
% 3.74/0.99      | sK8 != sK8
% 3.74/0.99      | v1_funct_2(sK8,X1,X0) = iProver_top
% 3.74/0.99      | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1484,plain,
% 3.74/0.99      ( sK8 != sK8
% 3.74/0.99      | k1_xboole_0 != sK6
% 3.74/0.99      | k1_xboole_0 != sK5
% 3.74/0.99      | v1_funct_2(sK8,sK5,sK6) != iProver_top
% 3.74/0.99      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_1482]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1775,plain,
% 3.74/0.99      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_318]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_1776,plain,
% 3.74/0.99      ( sK5 != k1_xboole_0
% 3.74/0.99      | k1_xboole_0 = sK5
% 3.74/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_1775]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7236,plain,
% 3.74/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0 ),
% 3.74/0.99      inference(global_propositional_subsumption,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_7008,c_34,c_35,c_2,c_344,c_1484,c_1481,c_1522,c_1523,
% 3.74/0.99                 c_1592,c_1593,c_1773,c_1770,c_1776,c_2377,c_2538,c_3879,
% 3.74/0.99                 c_5511,c_5581,c_6421]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_7634,plain,
% 3.74/0.99      ( k1_relat_1(sK8) = k1_xboole_0 ),
% 3.74/0.99      inference(light_normalisation,[status(thm)],[c_6740,c_7236]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5491,plain,
% 3.74/0.99      ( ~ v1_xboole_0(X0)
% 3.74/0.99      | v1_xboole_0(k1_relat_1(sK8))
% 3.74/0.99      | k1_relat_1(sK8) != X0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_319]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_5493,plain,
% 3.74/0.99      ( v1_xboole_0(k1_relat_1(sK8))
% 3.74/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.74/0.99      | k1_relat_1(sK8) != k1_xboole_0 ),
% 3.74/0.99      inference(instantiation,[status(thm)],[c_5491]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_12,plain,
% 3.74/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.74/0.99      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 3.74/0.99      | ~ v1_relat_1(X1) ),
% 3.74/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_891,plain,
% 3.74/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.74/0.99      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.74/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.74/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_3288,plain,
% 3.74/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.74/0.99      | v1_relat_1(X1) != iProver_top
% 3.74/0.99      | v1_xboole_0(k1_relat_1(X1)) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_891,c_901]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4115,plain,
% 3.74/0.99      ( v1_relat_1(sK8) != iProver_top
% 3.74/0.99      | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.74/0.99      inference(superposition,[status(thm)],[c_2538,c_3288]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(c_4151,plain,
% 3.74/0.99      ( ~ v1_relat_1(sK8) | ~ v1_xboole_0(k1_relat_1(sK8)) ),
% 3.74/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4115]) ).
% 3.74/0.99  
% 3.74/0.99  cnf(contradiction,plain,
% 3.74/0.99      ( $false ),
% 3.74/0.99      inference(minisat,
% 3.74/0.99                [status(thm)],
% 3.74/0.99                [c_7634,c_5493,c_4151,c_1592,c_1522,c_2]) ).
% 3.74/0.99  
% 3.74/0.99  
% 3.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/0.99  
% 3.74/0.99  ------                               Statistics
% 3.74/0.99  
% 3.74/0.99  ------ Selected
% 3.74/0.99  
% 3.74/0.99  total_time:                             0.333
% 3.74/0.99  
%------------------------------------------------------------------------------

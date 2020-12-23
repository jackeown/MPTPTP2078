%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:02 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  162 (1394 expanded)
%              Number of clauses        :   83 ( 431 expanded)
%              Number of leaves         :   22 ( 339 expanded)
%              Depth                    :   27
%              Number of atoms          :  578 (7433 expanded)
%              Number of equality atoms :  235 (2009 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f65,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
        & r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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

fof(f66,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f62,f65,f64,f63])).

fof(f97,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f127,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f45,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f45])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK9
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK8,X5) != X4
              | ~ r2_hidden(X5,sK7)
              | ~ m1_subset_1(X5,sK5) )
          & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7)) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ m1_subset_1(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f46,f69,f68])).

fof(f117,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f70])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f20,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f116,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f96,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f128,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f115,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f70])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f70])).

fof(f98,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f126,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f119,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ m1_subset_1(X5,sK5) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f81])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1794,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1779,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1789,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4166,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1779,c_1789])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1782,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2359,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_1782])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2376,plain,
    ( ~ v1_funct_2(sK8,sK5,sK6)
    | k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2359])).

cnf(c_2489,plain,
    ( sK6 = k1_xboole_0
    | k1_relset_1(sK5,sK6,sK8) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2359,c_47,c_2376])).

cnf(c_2490,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2489])).

cnf(c_4275,plain,
    ( k1_relat_1(sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4166,c_2490])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1793,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4802,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4275,c_1793])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_49,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_51,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2252,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2253,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2252])).

cnf(c_5321,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4802,c_49,c_51,c_2253])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1814,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5331,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK4(sK8,X0,X1),sK5) = iProver_top
    | r2_hidden(X1,k9_relat_1(sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5321,c_1814])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1788,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3918,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_1779,c_1788])).

cnf(c_45,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1780,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4390,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3918,c_1780])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1795,plain,
    ( k1_funct_1(X0,sK4(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6852,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4390,c_1795])).

cnf(c_7365,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6852,c_49,c_51,c_2253])).

cnf(c_44,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1781,plain,
    ( k1_funct_1(sK8,X0) != sK9
    | m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_7368,plain,
    ( m1_subset_1(sK4(sK8,sK7,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7365,c_1781])).

cnf(c_7373,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5331,c_7368])).

cnf(c_7500,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7373,c_4390])).

cnf(c_7501,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_7500])).

cnf(c_7506,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_7501])).

cnf(c_7988,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7506,c_49,c_51,c_2253,c_4390])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1819,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1821,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3316,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1819,c_1821])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1812,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3121,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_1812])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1816,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4959,plain,
    ( k2_zfmisc_1(sK5,sK6) = sK8
    | r1_tarski(k2_zfmisc_1(sK5,sK6),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_1816])).

cnf(c_5130,plain,
    ( k2_zfmisc_1(sK5,sK6) = sK8
    | v1_xboole_0(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3316,c_4959])).

cnf(c_7995,plain,
    ( k2_zfmisc_1(sK5,k1_xboole_0) = sK8
    | v1_xboole_0(k2_zfmisc_1(sK5,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7988,c_5130])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_8029,plain,
    ( sK8 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7995,c_8])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_162,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8601,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8029,c_162])).

cnf(c_8612,plain,
    ( r2_hidden(sK9,k9_relat_1(k1_xboole_0,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8601,c_4390])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1805,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1818,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6893,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_1818])).

cnf(c_7994,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK5,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7988,c_6893])).

cnf(c_8034,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7994,c_8])).

cnf(c_7085,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6893,c_1821])).

cnf(c_7993,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK5,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7988,c_7085])).

cnf(c_8039,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7993,c_8])).

cnf(c_9510,plain,
    ( r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8034,c_162,c_8039])).

cnf(c_9514,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9510,c_8601])).

cnf(c_11868,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_9514])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1808,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2429,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1808])).

cnf(c_12492,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11868,c_2429])).

cnf(c_12508,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_8612,c_12492])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:38:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.53/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/1.00  
% 3.53/1.00  ------  iProver source info
% 3.53/1.00  
% 3.53/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.53/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/1.00  git: non_committed_changes: false
% 3.53/1.00  git: last_make_outside_of_git: false
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  ------ Parsing...
% 3.53/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/1.00  ------ Proving...
% 3.53/1.00  ------ Problem Properties 
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  clauses                                 48
% 3.53/1.00  conjectures                             5
% 3.53/1.00  EPR                                     9
% 3.53/1.00  Horn                                    39
% 3.53/1.00  unary                                   9
% 3.53/1.00  binary                                  11
% 3.53/1.00  lits                                    137
% 3.53/1.00  lits eq                                 25
% 3.53/1.00  fd_pure                                 0
% 3.53/1.00  fd_pseudo                               0
% 3.53/1.00  fd_cond                                 4
% 3.53/1.00  fd_pseudo_cond                          5
% 3.53/1.00  AC symbols                              0
% 3.53/1.00  
% 3.53/1.00  ------ Input Options Time Limit: Unbounded
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  Current options:
% 3.53/1.00  ------ 
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ Proving...
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS status Theorem for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00   Resolution empty clause
% 3.53/1.00  
% 3.53/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  fof(f14,axiom,(
% 3.53/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f36,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f14])).
% 3.53/1.00  
% 3.53/1.00  fof(f37,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.53/1.00    inference(flattening,[],[f36])).
% 3.53/1.00  
% 3.53/1.00  fof(f61,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.53/1.00    inference(nnf_transformation,[],[f37])).
% 3.53/1.00  
% 3.53/1.00  fof(f62,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.53/1.00    inference(rectify,[],[f61])).
% 3.53/1.00  
% 3.53/1.00  fof(f65,plain,(
% 3.53/1.00    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f64,plain,(
% 3.53/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f63,plain,(
% 3.53/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK2(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f66,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f62,f65,f64,f63])).
% 3.53/1.00  
% 3.53/1.00  fof(f97,plain,(
% 3.53/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f66])).
% 3.53/1.00  
% 3.53/1.00  fof(f127,plain,(
% 3.53/1.00    ( ! [X6,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f97])).
% 3.53/1.00  
% 3.53/1.00  fof(f21,conjecture,(
% 3.53/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f22,negated_conjecture,(
% 3.53/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.53/1.00    inference(negated_conjecture,[],[f21])).
% 3.53/1.00  
% 3.53/1.00  fof(f45,plain,(
% 3.53/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.53/1.00    inference(ennf_transformation,[],[f22])).
% 3.53/1.00  
% 3.53/1.00  fof(f46,plain,(
% 3.53/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.53/1.00    inference(flattening,[],[f45])).
% 3.53/1.00  
% 3.53/1.00  fof(f69,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f68,plain,(
% 3.53/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f70,plain,(
% 3.53/1.00    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f46,f69,f68])).
% 3.53/1.00  
% 3.53/1.00  fof(f117,plain,(
% 3.53/1.00    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.53/1.00    inference(cnf_transformation,[],[f70])).
% 3.53/1.00  
% 3.53/1.00  fof(f18,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f41,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f18])).
% 3.53/1.00  
% 3.53/1.00  fof(f107,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f41])).
% 3.53/1.00  
% 3.53/1.00  fof(f20,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f43,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f20])).
% 3.53/1.00  
% 3.53/1.00  fof(f44,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(flattening,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f67,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(nnf_transformation,[],[f44])).
% 3.53/1.00  
% 3.53/1.00  fof(f109,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f67])).
% 3.53/1.00  
% 3.53/1.00  fof(f116,plain,(
% 3.53/1.00    v1_funct_2(sK8,sK5,sK6)),
% 3.53/1.00    inference(cnf_transformation,[],[f70])).
% 3.53/1.00  
% 3.53/1.00  fof(f96,plain,(
% 3.53/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f66])).
% 3.53/1.00  
% 3.53/1.00  fof(f128,plain,(
% 3.53/1.00    ( ! [X6,X0,X1] : (r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f96])).
% 3.53/1.00  
% 3.53/1.00  fof(f115,plain,(
% 3.53/1.00    v1_funct_1(sK8)),
% 3.53/1.00    inference(cnf_transformation,[],[f70])).
% 3.53/1.00  
% 3.53/1.00  fof(f16,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f39,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f16])).
% 3.53/1.00  
% 3.53/1.00  fof(f105,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f39])).
% 3.53/1.00  
% 3.53/1.00  fof(f6,axiom,(
% 3.53/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f27,plain,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.53/1.00    inference(ennf_transformation,[],[f6])).
% 3.53/1.00  
% 3.53/1.00  fof(f82,plain,(
% 3.53/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f27])).
% 3.53/1.00  
% 3.53/1.00  fof(f19,axiom,(
% 3.53/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f42,plain,(
% 3.53/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f19])).
% 3.53/1.00  
% 3.53/1.00  fof(f108,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f42])).
% 3.53/1.00  
% 3.53/1.00  fof(f118,plain,(
% 3.53/1.00    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 3.53/1.00    inference(cnf_transformation,[],[f70])).
% 3.53/1.00  
% 3.53/1.00  fof(f98,plain,(
% 3.53/1.00    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f66])).
% 3.53/1.00  
% 3.53/1.00  fof(f126,plain,(
% 3.53/1.00    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f98])).
% 3.53/1.00  
% 3.53/1.00  fof(f119,plain,(
% 3.53/1.00    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f70])).
% 3.53/1.00  
% 3.53/1.00  fof(f2,axiom,(
% 3.53/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f26,plain,(
% 3.53/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f2])).
% 3.53/1.00  
% 3.53/1.00  fof(f47,plain,(
% 3.53/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/1.00    inference(nnf_transformation,[],[f26])).
% 3.53/1.00  
% 3.53/1.00  fof(f48,plain,(
% 3.53/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/1.00    inference(rectify,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f49,plain,(
% 3.53/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f50,plain,(
% 3.53/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 3.53/1.00  
% 3.53/1.00  fof(f73,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f50])).
% 3.53/1.00  
% 3.53/1.00  fof(f1,axiom,(
% 3.53/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f23,plain,(
% 3.53/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.53/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.53/1.00  
% 3.53/1.00  fof(f25,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f23])).
% 3.53/1.00  
% 3.53/1.00  fof(f71,plain,(
% 3.53/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f25])).
% 3.53/1.00  
% 3.53/1.00  fof(f7,axiom,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f55,plain,(
% 3.53/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.53/1.00    inference(nnf_transformation,[],[f7])).
% 3.53/1.00  
% 3.53/1.00  fof(f83,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f55])).
% 3.53/1.00  
% 3.53/1.00  fof(f4,axiom,(
% 3.53/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f51,plain,(
% 3.53/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/1.00    inference(nnf_transformation,[],[f4])).
% 3.53/1.00  
% 3.53/1.00  fof(f52,plain,(
% 3.53/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/1.00    inference(flattening,[],[f51])).
% 3.53/1.00  
% 3.53/1.00  fof(f78,plain,(
% 3.53/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f5,axiom,(
% 3.53/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f53,plain,(
% 3.53/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.53/1.00    inference(nnf_transformation,[],[f5])).
% 3.53/1.00  
% 3.53/1.00  fof(f54,plain,(
% 3.53/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.53/1.00    inference(flattening,[],[f53])).
% 3.53/1.00  
% 3.53/1.00  fof(f81,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.53/1.00    inference(cnf_transformation,[],[f54])).
% 3.53/1.00  
% 3.53/1.00  fof(f122,plain,(
% 3.53/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f81])).
% 3.53/1.00  
% 3.53/1.00  fof(f3,axiom,(
% 3.53/1.00    v1_xboole_0(k1_xboole_0)),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f75,plain,(
% 3.53/1.00    v1_xboole_0(k1_xboole_0)),
% 3.53/1.00    inference(cnf_transformation,[],[f3])).
% 3.53/1.00  
% 3.53/1.00  fof(f11,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f31,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.53/1.00    inference(ennf_transformation,[],[f11])).
% 3.53/1.00  
% 3.53/1.00  fof(f57,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.53/1.00    inference(nnf_transformation,[],[f31])).
% 3.53/1.00  
% 3.53/1.00  fof(f58,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.53/1.00    inference(rectify,[],[f57])).
% 3.53/1.00  
% 3.53/1.00  fof(f59,plain,(
% 3.53/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f60,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).
% 3.53/1.00  
% 3.53/1.00  fof(f90,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f60])).
% 3.53/1.00  
% 3.53/1.00  fof(f72,plain,(
% 3.53/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f50])).
% 3.53/1.00  
% 3.53/1.00  fof(f10,axiom,(
% 3.53/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f88,plain,(
% 3.53/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f10])).
% 3.53/1.00  
% 3.53/1.00  cnf(c_31,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | r2_hidden(sK4(X1,X2,X0),X2)
% 3.53/1.00      | ~ v1_funct_1(X1)
% 3.53/1.00      | ~ v1_relat_1(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f127]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1794,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.53/1.00      | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
% 3.53/1.00      | v1_funct_1(X1) != iProver_top
% 3.53/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_46,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1779,plain,
% 3.53/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_36,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1789,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4166,plain,
% 3.53/1.00      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1779,c_1789]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_43,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.53/1.00      | k1_xboole_0 = X2 ),
% 3.53/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1782,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.53/1.00      | k1_xboole_0 = X1
% 3.53/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2359,plain,
% 3.53/1.00      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.53/1.00      | sK6 = k1_xboole_0
% 3.53/1.00      | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1779,c_1782]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_47,negated_conjecture,
% 3.53/1.00      ( v1_funct_2(sK8,sK5,sK6) ),
% 3.53/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2376,plain,
% 3.53/1.00      ( ~ v1_funct_2(sK8,sK5,sK6)
% 3.53/1.00      | k1_relset_1(sK5,sK6,sK8) = sK5
% 3.53/1.00      | sK6 = k1_xboole_0 ),
% 3.53/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2359]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2489,plain,
% 3.53/1.00      ( sK6 = k1_xboole_0 | k1_relset_1(sK5,sK6,sK8) = sK5 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_2359,c_47,c_2376]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2490,plain,
% 3.53/1.00      ( k1_relset_1(sK5,sK6,sK8) = sK5 | sK6 = k1_xboole_0 ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_2489]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4275,plain,
% 3.53/1.00      ( k1_relat_1(sK8) = sK5 | sK6 = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_4166,c_2490]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_32,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1))
% 3.53/1.00      | ~ v1_funct_1(X1)
% 3.53/1.00      | ~ v1_relat_1(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f128]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1793,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.53/1.00      | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 3.53/1.00      | v1_funct_1(X1) != iProver_top
% 3.53/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4802,plain,
% 3.53/1.00      ( sK6 = k1_xboole_0
% 3.53/1.00      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top
% 3.53/1.00      | v1_funct_1(sK8) != iProver_top
% 3.53/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_4275,c_1793]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_48,negated_conjecture,
% 3.53/1.00      ( v1_funct_1(sK8) ),
% 3.53/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_49,plain,
% 3.53/1.00      ( v1_funct_1(sK8) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_51,plain,
% 3.53/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_34,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2252,plain,
% 3.53/1.00      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.53/1.00      | v1_relat_1(sK8) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_34]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2253,plain,
% 3.53/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.53/1.00      | v1_relat_1(sK8) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2252]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5321,plain,
% 3.53/1.00      ( sK6 = k1_xboole_0
% 3.53/1.00      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_4802,c_49,c_51,c_2253]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11,plain,
% 3.53/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1814,plain,
% 3.53/1.00      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5331,plain,
% 3.53/1.00      ( sK6 = k1_xboole_0
% 3.53/1.00      | m1_subset_1(sK4(sK8,X0,X1),sK5) = iProver_top
% 3.53/1.00      | r2_hidden(X1,k9_relat_1(sK8,X0)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_5321,c_1814]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_37,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1788,plain,
% 3.53/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3918,plain,
% 3.53/1.00      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1779,c_1788]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_45,negated_conjecture,
% 3.53/1.00      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f118]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1780,plain,
% 3.53/1.00      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4390,plain,
% 3.53/1.00      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_3918,c_1780]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_30,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | ~ v1_funct_1(X1)
% 3.53/1.00      | ~ v1_relat_1(X1)
% 3.53/1.00      | k1_funct_1(X1,sK4(X1,X2,X0)) = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f126]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1795,plain,
% 3.53/1.00      ( k1_funct_1(X0,sK4(X0,X1,X2)) = X2
% 3.53/1.00      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 3.53/1.00      | v1_funct_1(X0) != iProver_top
% 3.53/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6852,plain,
% 3.53/1.00      ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9
% 3.53/1.00      | v1_funct_1(sK8) != iProver_top
% 3.53/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_4390,c_1795]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7365,plain,
% 3.53/1.00      ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_6852,c_49,c_51,c_2253]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_44,negated_conjecture,
% 3.53/1.00      ( ~ m1_subset_1(X0,sK5)
% 3.53/1.00      | ~ r2_hidden(X0,sK7)
% 3.53/1.00      | k1_funct_1(sK8,X0) != sK9 ),
% 3.53/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1781,plain,
% 3.53/1.00      ( k1_funct_1(sK8,X0) != sK9
% 3.53/1.00      | m1_subset_1(X0,sK5) != iProver_top
% 3.53/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7368,plain,
% 3.53/1.00      ( m1_subset_1(sK4(sK8,sK7,sK9),sK5) != iProver_top
% 3.53/1.00      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7365,c_1781]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7373,plain,
% 3.53/1.00      ( sK6 = k1_xboole_0
% 3.53/1.00      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
% 3.53/1.00      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_5331,c_7368]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7500,plain,
% 3.53/1.00      ( r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top | sK6 = k1_xboole_0 ),
% 3.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7373,c_4390]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7501,plain,
% 3.53/1.00      ( sK6 = k1_xboole_0 | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_7500]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7506,plain,
% 3.53/1.00      ( sK6 = k1_xboole_0
% 3.53/1.00      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.53/1.00      | v1_funct_1(sK8) != iProver_top
% 3.53/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1794,c_7501]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7988,plain,
% 3.53/1.00      ( sK6 = k1_xboole_0 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_7506,c_49,c_51,c_2253,c_4390]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1819,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.53/1.00      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_0,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1821,plain,
% 3.53/1.00      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3316,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1819,c_1821]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_13,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1812,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.53/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3121,plain,
% 3.53/1.00      ( r1_tarski(sK8,k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1779,c_1812]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5,plain,
% 3.53/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.53/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1816,plain,
% 3.53/1.00      ( X0 = X1
% 3.53/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.53/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4959,plain,
% 3.53/1.00      ( k2_zfmisc_1(sK5,sK6) = sK8
% 3.53/1.00      | r1_tarski(k2_zfmisc_1(sK5,sK6),sK8) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3121,c_1816]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5130,plain,
% 3.53/1.00      ( k2_zfmisc_1(sK5,sK6) = sK8
% 3.53/1.00      | v1_xboole_0(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3316,c_4959]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7995,plain,
% 3.53/1.00      ( k2_zfmisc_1(sK5,k1_xboole_0) = sK8
% 3.53/1.00      | v1_xboole_0(k2_zfmisc_1(sK5,k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7988,c_5130]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8,plain,
% 3.53/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f122]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8029,plain,
% 3.53/1.00      ( sK8 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7995,c_8]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4,plain,
% 3.53/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_162,plain,
% 3.53/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8601,plain,
% 3.53/1.00      ( sK8 = k1_xboole_0 ),
% 3.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8029,c_162]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8612,plain,
% 3.53/1.00      ( r2_hidden(sK9,k9_relat_1(k1_xboole_0,sK7)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_8601,c_4390]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_20,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.53/1.00      | ~ v1_relat_1(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1805,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.53/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.53/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3,plain,
% 3.53/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1818,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.53/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.53/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6893,plain,
% 3.53/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
% 3.53/1.00      | r2_hidden(X0,sK8) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3121,c_1818]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7994,plain,
% 3.53/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK5,k1_xboole_0)) = iProver_top
% 3.53/1.00      | r2_hidden(X0,sK8) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7988,c_6893]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8034,plain,
% 3.53/1.00      ( r2_hidden(X0,sK8) != iProver_top
% 3.53/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7994,c_8]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7085,plain,
% 3.53/1.00      ( r2_hidden(X0,sK8) != iProver_top
% 3.53/1.00      | v1_xboole_0(k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_6893,c_1821]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7993,plain,
% 3.53/1.00      ( r2_hidden(X0,sK8) != iProver_top
% 3.53/1.00      | v1_xboole_0(k2_zfmisc_1(sK5,k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7988,c_7085]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8039,plain,
% 3.53/1.00      ( r2_hidden(X0,sK8) != iProver_top
% 3.53/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7993,c_8]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9510,plain,
% 3.53/1.00      ( r2_hidden(X0,sK8) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_8034,c_162,c_8039]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9514,plain,
% 3.53/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_9510,c_8601]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11868,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
% 3.53/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1805,c_9514]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17,plain,
% 3.53/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1808,plain,
% 3.53/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2429,plain,
% 3.53/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_8,c_1808]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12492,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_11868,c_2429]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12508,plain,
% 3.53/1.00      ( $false ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_8612,c_12492]) ).
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  ------                               Statistics
% 3.53/1.00  
% 3.53/1.00  ------ Selected
% 3.53/1.00  
% 3.53/1.00  total_time:                             0.323
% 3.53/1.00  
%------------------------------------------------------------------------------

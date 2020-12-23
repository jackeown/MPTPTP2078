%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:01 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 711 expanded)
%              Number of clauses        :   74 ( 211 expanded)
%              Number of leaves         :   24 ( 178 expanded)
%              Depth                    :   20
%              Number of atoms          :  620 (3804 expanded)
%              Number of equality atoms :  231 ( 937 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f66,plain,(
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
    inference(rectify,[],[f65])).

fof(f69,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
        & r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
              ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK4(X0,X1,X2)) = sK3(X0,X1,X2)
                  & r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
                    & r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f66,f69,f68,f67])).

fof(f108,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f150,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f108])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f81,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

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
    inference(ennf_transformation,[],[f23])).

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

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK16
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK16,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,
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
              ( k1_funct_1(sK15,X5) != X4
              | ~ r2_hidden(X5,sK14)
              | ~ m1_subset_1(X5,sK12) )
          & r2_hidden(X4,k7_relset_1(sK12,sK13,sK15,sK14)) )
      & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13)))
      & v1_funct_2(sK15,sK12,sK13)
      & v1_funct_1(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,
    ( ! [X5] :
        ( k1_funct_1(sK15,X5) != sK16
        | ~ r2_hidden(X5,sK14)
        | ~ m1_subset_1(X5,sK12) )
    & r2_hidden(sK16,k7_relset_1(sK12,sK13,sK15,sK14))
    & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13)))
    & v1_funct_2(sK15,sK12,sK13)
    & v1_funct_1(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14,sK15,sK16])],[f46,f83,f82])).

fof(f141,plain,(
    v1_funct_2(sK15,sK12,sK13) ),
    inference(cnf_transformation,[],[f84])).

fof(f142,plain,(
    m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13))) ),
    inference(cnf_transformation,[],[f84])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f107,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f151,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f140,plain,(
    v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f84])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f143,plain,(
    r2_hidden(sK16,k7_relset_1(sK12,sK13,sK15,sK14)) ),
    inference(cnf_transformation,[],[f84])).

fof(f109,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f149,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f144,plain,(
    ! [X5] :
      ( k1_funct_1(sK15,X5) != sK16
      | ~ r2_hidden(X5,sK14)
      | ~ m1_subset_1(X5,sK12) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f12,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f72,plain,(
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
    inference(rectify,[],[f71])).

fof(f75,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X5)) = X5
        & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) = X2
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
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
              ( k1_funct_1(X0,X3) != sK6(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK6(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK6(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK6(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK7(X0,X1)) = sK6(X0,X1)
                  & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK6(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK8(X0,X5)) = X5
                    & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f72,f75,f74,f73])).

fof(f117,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f152,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f117])).

fof(f153,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f152])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_9132,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_51,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_58,negated_conjecture,
    ( v1_funct_2(sK15,sK12,sK13) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_913,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK13 != X2
    | sK12 != X1
    | sK15 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_58])).

cnf(c_914,plain,
    ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13)))
    | k1_relset_1(sK12,sK13,sK15) = sK12
    | k1_xboole_0 = sK13 ),
    inference(unflattening,[status(thm)],[c_913])).

cnf(c_57,negated_conjecture,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13))) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_916,plain,
    ( k1_relset_1(sK12,sK13,sK15) = sK12
    | k1_xboole_0 = sK13 ),
    inference(global_propositional_subsumption,[status(thm)],[c_914,c_57])).

cnf(c_9112,plain,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_44,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_9117,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_12418,plain,
    ( k1_relset_1(sK12,sK13,sK15) = k1_relat_1(sK15) ),
    inference(superposition,[status(thm)],[c_9112,c_9117])).

cnf(c_12524,plain,
    ( k1_relat_1(sK15) = sK12
    | sK13 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_916,c_12418])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_9131,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_14981,plain,
    ( sK13 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK15,X1)) != iProver_top
    | r2_hidden(sK5(sK15,X1,X0),sK12) = iProver_top
    | v1_funct_1(sK15) != iProver_top
    | v1_relat_1(sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_12524,c_9131])).

cnf(c_59,negated_conjecture,
    ( v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_60,plain,
    ( v1_funct_1(sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_9119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_10774,plain,
    ( v1_relat_1(sK15) = iProver_top ),
    inference(superposition,[status(thm)],[c_9112,c_9119])).

cnf(c_15381,plain,
    ( sK13 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK15,X1)) != iProver_top
    | r2_hidden(sK5(sK15,X1,X0),sK12) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14981,c_60,c_10774])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_9146,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15388,plain,
    ( sK13 = k1_xboole_0
    | m1_subset_1(sK5(sK15,X0,X1),sK12) = iProver_top
    | r2_hidden(X1,k9_relat_1(sK15,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15381,c_9146])).

cnf(c_45,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_9116,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_12516,plain,
    ( k7_relset_1(sK12,sK13,sK15,X0) = k9_relat_1(sK15,X0) ),
    inference(superposition,[status(thm)],[c_9112,c_9116])).

cnf(c_56,negated_conjecture,
    ( r2_hidden(sK16,k7_relset_1(sK12,sK13,sK15,sK14)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_9113,plain,
    ( r2_hidden(sK16,k7_relset_1(sK12,sK13,sK15,sK14)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_12622,plain,
    ( r2_hidden(sK16,k9_relat_1(sK15,sK14)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12516,c_9113])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f149])).

cnf(c_9133,plain,
    ( k1_funct_1(X0,sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14906,plain,
    ( k1_funct_1(sK15,sK5(sK15,sK14,sK16)) = sK16
    | v1_funct_1(sK15) != iProver_top
    | v1_relat_1(sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_12622,c_9133])).

cnf(c_15227,plain,
    ( k1_funct_1(sK15,sK5(sK15,sK14,sK16)) = sK16 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14906,c_60,c_10774])).

cnf(c_55,negated_conjecture,
    ( ~ m1_subset_1(X0,sK12)
    | ~ r2_hidden(X0,sK14)
    | k1_funct_1(sK15,X0) != sK16 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_9114,plain,
    ( k1_funct_1(sK15,X0) != sK16
    | m1_subset_1(X0,sK12) != iProver_top
    | r2_hidden(X0,sK14) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_15230,plain,
    ( m1_subset_1(sK5(sK15,sK14,sK16),sK12) != iProver_top
    | r2_hidden(sK5(sK15,sK14,sK16),sK14) != iProver_top ),
    inference(superposition,[status(thm)],[c_15227,c_9114])).

cnf(c_25184,plain,
    ( sK13 = k1_xboole_0
    | r2_hidden(sK5(sK15,sK14,sK16),sK14) != iProver_top
    | r2_hidden(sK16,k9_relat_1(sK15,sK14)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15388,c_15230])).

cnf(c_25845,plain,
    ( r2_hidden(sK5(sK15,sK14,sK16),sK14) != iProver_top
    | sK13 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25184,c_12622])).

cnf(c_25846,plain,
    ( sK13 = k1_xboole_0
    | r2_hidden(sK5(sK15,sK14,sK16),sK14) != iProver_top ),
    inference(renaming,[status(thm)],[c_25845])).

cnf(c_25849,plain,
    ( sK13 = k1_xboole_0
    | r2_hidden(sK16,k9_relat_1(sK15,sK14)) != iProver_top
    | v1_funct_1(sK15) != iProver_top
    | v1_relat_1(sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_9132,c_25846])).

cnf(c_27416,plain,
    ( sK13 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25849,c_60,c_10774,c_12622])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_9127,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_42,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_769,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_42,c_16])).

cnf(c_773,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_769,c_41])).

cnf(c_774,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_773])).

cnf(c_9110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_11996,plain,
    ( r1_tarski(k2_relat_1(sK15),sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_9112,c_9110])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_9153,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13331,plain,
    ( r2_hidden(X0,k2_relat_1(sK15)) != iProver_top
    | r2_hidden(X0,sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_11996,c_9153])).

cnf(c_14138,plain,
    ( r2_hidden(X0,k1_relat_1(sK15)) != iProver_top
    | r2_hidden(k1_funct_1(sK15,X0),sK13) = iProver_top
    | v1_funct_1(sK15) != iProver_top
    | v1_relat_1(sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_9127,c_13331])).

cnf(c_15807,plain,
    ( r2_hidden(X0,k1_relat_1(sK15)) != iProver_top
    | r2_hidden(k1_funct_1(sK15,X0),sK13) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14138,c_60,c_10774])).

cnf(c_15813,plain,
    ( r2_hidden(sK5(sK15,sK14,sK16),k1_relat_1(sK15)) != iProver_top
    | r2_hidden(sK16,sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_15227,c_15807])).

cnf(c_15825,plain,
    ( sK13 = k1_xboole_0
    | r2_hidden(sK5(sK15,sK14,sK16),sK12) != iProver_top
    | r2_hidden(sK16,sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_12524,c_15813])).

cnf(c_15824,plain,
    ( r2_hidden(sK16,k9_relat_1(sK15,sK14)) != iProver_top
    | r2_hidden(sK16,sK13) = iProver_top
    | v1_funct_1(sK15) != iProver_top
    | v1_relat_1(sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_9131,c_15813])).

cnf(c_16447,plain,
    ( r2_hidden(sK16,sK13) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15825,c_60,c_10774,c_12622,c_15824])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_9156,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16451,plain,
    ( v1_xboole_0(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_16447,c_9156])).

cnf(c_27433,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27416,c_16451])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_9157,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_9150,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_40,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_9120,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_10340,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9150,c_9120])).

cnf(c_10440,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9157,c_10340])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27433,c_10440])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:36:15 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 7.58/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/1.48  
% 7.58/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.48  
% 7.58/1.48  ------  iProver source info
% 7.58/1.48  
% 7.58/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.48  git: non_committed_changes: false
% 7.58/1.48  git: last_make_outside_of_git: false
% 7.58/1.48  
% 7.58/1.48  ------ 
% 7.58/1.48  
% 7.58/1.48  ------ Input Options
% 7.58/1.48  
% 7.58/1.48  --out_options                           all
% 7.58/1.48  --tptp_safe_out                         true
% 7.58/1.48  --problem_path                          ""
% 7.58/1.48  --include_path                          ""
% 7.58/1.48  --clausifier                            res/vclausify_rel
% 7.58/1.48  --clausifier_options                    ""
% 7.58/1.48  --stdin                                 false
% 7.58/1.48  --stats_out                             all
% 7.58/1.48  
% 7.58/1.48  ------ General Options
% 7.58/1.48  
% 7.58/1.48  --fof                                   false
% 7.58/1.48  --time_out_real                         305.
% 7.58/1.48  --time_out_virtual                      -1.
% 7.58/1.48  --symbol_type_check                     false
% 7.58/1.48  --clausify_out                          false
% 7.58/1.48  --sig_cnt_out                           false
% 7.58/1.48  --trig_cnt_out                          false
% 7.58/1.48  --trig_cnt_out_tolerance                1.
% 7.58/1.48  --trig_cnt_out_sk_spl                   false
% 7.58/1.48  --abstr_cl_out                          false
% 7.58/1.48  
% 7.58/1.48  ------ Global Options
% 7.58/1.48  
% 7.58/1.48  --schedule                              default
% 7.58/1.48  --add_important_lit                     false
% 7.58/1.48  --prop_solver_per_cl                    1000
% 7.58/1.48  --min_unsat_core                        false
% 7.58/1.48  --soft_assumptions                      false
% 7.58/1.48  --soft_lemma_size                       3
% 7.58/1.48  --prop_impl_unit_size                   0
% 7.58/1.48  --prop_impl_unit                        []
% 7.58/1.48  --share_sel_clauses                     true
% 7.58/1.48  --reset_solvers                         false
% 7.58/1.48  --bc_imp_inh                            [conj_cone]
% 7.58/1.48  --conj_cone_tolerance                   3.
% 7.58/1.48  --extra_neg_conj                        none
% 7.58/1.48  --large_theory_mode                     true
% 7.58/1.48  --prolific_symb_bound                   200
% 7.58/1.48  --lt_threshold                          2000
% 7.58/1.48  --clause_weak_htbl                      true
% 7.58/1.48  --gc_record_bc_elim                     false
% 7.58/1.48  
% 7.58/1.48  ------ Preprocessing Options
% 7.58/1.48  
% 7.58/1.48  --preprocessing_flag                    true
% 7.58/1.48  --time_out_prep_mult                    0.1
% 7.58/1.48  --splitting_mode                        input
% 7.58/1.48  --splitting_grd                         true
% 7.58/1.48  --splitting_cvd                         false
% 7.58/1.48  --splitting_cvd_svl                     false
% 7.58/1.48  --splitting_nvd                         32
% 7.58/1.48  --sub_typing                            true
% 7.58/1.48  --prep_gs_sim                           true
% 7.58/1.48  --prep_unflatten                        true
% 7.58/1.48  --prep_res_sim                          true
% 7.58/1.48  --prep_upred                            true
% 7.58/1.48  --prep_sem_filter                       exhaustive
% 7.58/1.48  --prep_sem_filter_out                   false
% 7.58/1.48  --pred_elim                             true
% 7.58/1.48  --res_sim_input                         true
% 7.58/1.48  --eq_ax_congr_red                       true
% 7.58/1.48  --pure_diseq_elim                       true
% 7.58/1.48  --brand_transform                       false
% 7.58/1.48  --non_eq_to_eq                          false
% 7.58/1.48  --prep_def_merge                        true
% 7.58/1.48  --prep_def_merge_prop_impl              false
% 7.58/1.48  --prep_def_merge_mbd                    true
% 7.58/1.48  --prep_def_merge_tr_red                 false
% 7.58/1.48  --prep_def_merge_tr_cl                  false
% 7.58/1.48  --smt_preprocessing                     true
% 7.58/1.48  --smt_ac_axioms                         fast
% 7.58/1.48  --preprocessed_out                      false
% 7.58/1.48  --preprocessed_stats                    false
% 7.58/1.48  
% 7.58/1.48  ------ Abstraction refinement Options
% 7.58/1.48  
% 7.58/1.48  --abstr_ref                             []
% 7.58/1.48  --abstr_ref_prep                        false
% 7.58/1.48  --abstr_ref_until_sat                   false
% 7.58/1.48  --abstr_ref_sig_restrict                funpre
% 7.58/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.48  --abstr_ref_under                       []
% 7.58/1.48  
% 7.58/1.48  ------ SAT Options
% 7.58/1.48  
% 7.58/1.48  --sat_mode                              false
% 7.58/1.48  --sat_fm_restart_options                ""
% 7.58/1.48  --sat_gr_def                            false
% 7.58/1.48  --sat_epr_types                         true
% 7.58/1.48  --sat_non_cyclic_types                  false
% 7.58/1.48  --sat_finite_models                     false
% 7.58/1.48  --sat_fm_lemmas                         false
% 7.58/1.48  --sat_fm_prep                           false
% 7.58/1.48  --sat_fm_uc_incr                        true
% 7.58/1.48  --sat_out_model                         small
% 7.58/1.48  --sat_out_clauses                       false
% 7.58/1.48  
% 7.58/1.48  ------ QBF Options
% 7.58/1.48  
% 7.58/1.48  --qbf_mode                              false
% 7.58/1.48  --qbf_elim_univ                         false
% 7.58/1.48  --qbf_dom_inst                          none
% 7.58/1.48  --qbf_dom_pre_inst                      false
% 7.58/1.48  --qbf_sk_in                             false
% 7.58/1.48  --qbf_pred_elim                         true
% 7.58/1.48  --qbf_split                             512
% 7.58/1.48  
% 7.58/1.48  ------ BMC1 Options
% 7.58/1.48  
% 7.58/1.48  --bmc1_incremental                      false
% 7.58/1.48  --bmc1_axioms                           reachable_all
% 7.58/1.48  --bmc1_min_bound                        0
% 7.58/1.48  --bmc1_max_bound                        -1
% 7.58/1.48  --bmc1_max_bound_default                -1
% 7.58/1.48  --bmc1_symbol_reachability              true
% 7.58/1.48  --bmc1_property_lemmas                  false
% 7.58/1.48  --bmc1_k_induction                      false
% 7.58/1.48  --bmc1_non_equiv_states                 false
% 7.58/1.48  --bmc1_deadlock                         false
% 7.58/1.48  --bmc1_ucm                              false
% 7.58/1.48  --bmc1_add_unsat_core                   none
% 7.58/1.48  --bmc1_unsat_core_children              false
% 7.58/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.48  --bmc1_out_stat                         full
% 7.58/1.48  --bmc1_ground_init                      false
% 7.58/1.48  --bmc1_pre_inst_next_state              false
% 7.58/1.48  --bmc1_pre_inst_state                   false
% 7.58/1.48  --bmc1_pre_inst_reach_state             false
% 7.58/1.48  --bmc1_out_unsat_core                   false
% 7.58/1.48  --bmc1_aig_witness_out                  false
% 7.58/1.48  --bmc1_verbose                          false
% 7.58/1.48  --bmc1_dump_clauses_tptp                false
% 7.58/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.48  --bmc1_dump_file                        -
% 7.58/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.48  --bmc1_ucm_extend_mode                  1
% 7.58/1.48  --bmc1_ucm_init_mode                    2
% 7.58/1.48  --bmc1_ucm_cone_mode                    none
% 7.58/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.48  --bmc1_ucm_relax_model                  4
% 7.58/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.48  --bmc1_ucm_layered_model                none
% 7.58/1.48  --bmc1_ucm_max_lemma_size               10
% 7.58/1.48  
% 7.58/1.48  ------ AIG Options
% 7.58/1.48  
% 7.58/1.48  --aig_mode                              false
% 7.58/1.48  
% 7.58/1.48  ------ Instantiation Options
% 7.58/1.48  
% 7.58/1.48  --instantiation_flag                    true
% 7.58/1.48  --inst_sos_flag                         true
% 7.58/1.48  --inst_sos_phase                        true
% 7.58/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.48  --inst_lit_sel_side                     num_symb
% 7.58/1.48  --inst_solver_per_active                1400
% 7.58/1.48  --inst_solver_calls_frac                1.
% 7.58/1.48  --inst_passive_queue_type               priority_queues
% 7.58/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.48  --inst_passive_queues_freq              [25;2]
% 7.58/1.48  --inst_dismatching                      true
% 7.58/1.48  --inst_eager_unprocessed_to_passive     true
% 7.58/1.48  --inst_prop_sim_given                   true
% 7.58/1.48  --inst_prop_sim_new                     false
% 7.58/1.48  --inst_subs_new                         false
% 7.58/1.48  --inst_eq_res_simp                      false
% 7.58/1.48  --inst_subs_given                       false
% 7.58/1.48  --inst_orphan_elimination               true
% 7.58/1.48  --inst_learning_loop_flag               true
% 7.58/1.48  --inst_learning_start                   3000
% 7.58/1.48  --inst_learning_factor                  2
% 7.58/1.48  --inst_start_prop_sim_after_learn       3
% 7.58/1.48  --inst_sel_renew                        solver
% 7.58/1.48  --inst_lit_activity_flag                true
% 7.58/1.48  --inst_restr_to_given                   false
% 7.58/1.48  --inst_activity_threshold               500
% 7.58/1.48  --inst_out_proof                        true
% 7.58/1.48  
% 7.58/1.48  ------ Resolution Options
% 7.58/1.48  
% 7.58/1.48  --resolution_flag                       true
% 7.58/1.48  --res_lit_sel                           adaptive
% 7.58/1.48  --res_lit_sel_side                      none
% 7.58/1.48  --res_ordering                          kbo
% 7.58/1.48  --res_to_prop_solver                    active
% 7.58/1.48  --res_prop_simpl_new                    false
% 7.58/1.48  --res_prop_simpl_given                  true
% 7.58/1.48  --res_passive_queue_type                priority_queues
% 7.58/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.48  --res_passive_queues_freq               [15;5]
% 7.58/1.48  --res_forward_subs                      full
% 7.58/1.48  --res_backward_subs                     full
% 7.58/1.48  --res_forward_subs_resolution           true
% 7.58/1.48  --res_backward_subs_resolution          true
% 7.58/1.48  --res_orphan_elimination                true
% 7.58/1.48  --res_time_limit                        2.
% 7.58/1.48  --res_out_proof                         true
% 7.58/1.48  
% 7.58/1.48  ------ Superposition Options
% 7.58/1.48  
% 7.58/1.48  --superposition_flag                    true
% 7.58/1.48  --sup_passive_queue_type                priority_queues
% 7.58/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.48  --demod_completeness_check              fast
% 7.58/1.48  --demod_use_ground                      true
% 7.58/1.48  --sup_to_prop_solver                    passive
% 7.58/1.48  --sup_prop_simpl_new                    true
% 7.58/1.48  --sup_prop_simpl_given                  true
% 7.58/1.48  --sup_fun_splitting                     true
% 7.58/1.48  --sup_smt_interval                      50000
% 7.58/1.48  
% 7.58/1.48  ------ Superposition Simplification Setup
% 7.58/1.48  
% 7.58/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.48  --sup_immed_triv                        [TrivRules]
% 7.58/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.48  --sup_immed_bw_main                     []
% 7.58/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.48  --sup_input_bw                          []
% 7.58/1.48  
% 7.58/1.48  ------ Combination Options
% 7.58/1.48  
% 7.58/1.48  --comb_res_mult                         3
% 7.58/1.48  --comb_sup_mult                         2
% 7.58/1.48  --comb_inst_mult                        10
% 7.58/1.48  
% 7.58/1.48  ------ Debug Options
% 7.58/1.48  
% 7.58/1.48  --dbg_backtrace                         false
% 7.58/1.48  --dbg_dump_prop_clauses                 false
% 7.58/1.48  --dbg_dump_prop_clauses_file            -
% 7.58/1.48  --dbg_out_stat                          false
% 7.58/1.48  ------ Parsing...
% 7.58/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.48  
% 7.58/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.58/1.48  
% 7.58/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.48  
% 7.58/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.48  ------ Proving...
% 7.58/1.48  ------ Problem Properties 
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  clauses                                 54
% 7.58/1.48  conjectures                             4
% 7.58/1.48  EPR                                     8
% 7.58/1.48  Horn                                    41
% 7.58/1.48  unary                                   6
% 7.58/1.48  binary                                  18
% 7.58/1.48  lits                                    167
% 7.58/1.48  lits eq                                 32
% 7.58/1.48  fd_pure                                 0
% 7.58/1.48  fd_pseudo                               0
% 7.58/1.48  fd_cond                                 2
% 7.58/1.48  fd_pseudo_cond                          9
% 7.58/1.48  AC symbols                              0
% 7.58/1.48  
% 7.58/1.48  ------ Schedule dynamic 5 is on 
% 7.58/1.48  
% 7.58/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  ------ 
% 7.58/1.48  Current options:
% 7.58/1.48  ------ 
% 7.58/1.48  
% 7.58/1.48  ------ Input Options
% 7.58/1.48  
% 7.58/1.48  --out_options                           all
% 7.58/1.48  --tptp_safe_out                         true
% 7.58/1.48  --problem_path                          ""
% 7.58/1.48  --include_path                          ""
% 7.58/1.48  --clausifier                            res/vclausify_rel
% 7.58/1.48  --clausifier_options                    ""
% 7.58/1.48  --stdin                                 false
% 7.58/1.48  --stats_out                             all
% 7.58/1.48  
% 7.58/1.48  ------ General Options
% 7.58/1.48  
% 7.58/1.48  --fof                                   false
% 7.58/1.48  --time_out_real                         305.
% 7.58/1.48  --time_out_virtual                      -1.
% 7.58/1.48  --symbol_type_check                     false
% 7.58/1.48  --clausify_out                          false
% 7.58/1.48  --sig_cnt_out                           false
% 7.58/1.48  --trig_cnt_out                          false
% 7.58/1.48  --trig_cnt_out_tolerance                1.
% 7.58/1.48  --trig_cnt_out_sk_spl                   false
% 7.58/1.48  --abstr_cl_out                          false
% 7.58/1.48  
% 7.58/1.48  ------ Global Options
% 7.58/1.48  
% 7.58/1.48  --schedule                              default
% 7.58/1.48  --add_important_lit                     false
% 7.58/1.48  --prop_solver_per_cl                    1000
% 7.58/1.48  --min_unsat_core                        false
% 7.58/1.48  --soft_assumptions                      false
% 7.58/1.48  --soft_lemma_size                       3
% 7.58/1.48  --prop_impl_unit_size                   0
% 7.58/1.48  --prop_impl_unit                        []
% 7.58/1.48  --share_sel_clauses                     true
% 7.58/1.48  --reset_solvers                         false
% 7.58/1.48  --bc_imp_inh                            [conj_cone]
% 7.58/1.48  --conj_cone_tolerance                   3.
% 7.58/1.48  --extra_neg_conj                        none
% 7.58/1.48  --large_theory_mode                     true
% 7.58/1.48  --prolific_symb_bound                   200
% 7.58/1.48  --lt_threshold                          2000
% 7.58/1.48  --clause_weak_htbl                      true
% 7.58/1.48  --gc_record_bc_elim                     false
% 7.58/1.48  
% 7.58/1.48  ------ Preprocessing Options
% 7.58/1.48  
% 7.58/1.48  --preprocessing_flag                    true
% 7.58/1.48  --time_out_prep_mult                    0.1
% 7.58/1.48  --splitting_mode                        input
% 7.58/1.48  --splitting_grd                         true
% 7.58/1.48  --splitting_cvd                         false
% 7.58/1.48  --splitting_cvd_svl                     false
% 7.58/1.48  --splitting_nvd                         32
% 7.58/1.48  --sub_typing                            true
% 7.58/1.48  --prep_gs_sim                           true
% 7.58/1.48  --prep_unflatten                        true
% 7.58/1.48  --prep_res_sim                          true
% 7.58/1.48  --prep_upred                            true
% 7.58/1.48  --prep_sem_filter                       exhaustive
% 7.58/1.48  --prep_sem_filter_out                   false
% 7.58/1.48  --pred_elim                             true
% 7.58/1.48  --res_sim_input                         true
% 7.58/1.48  --eq_ax_congr_red                       true
% 7.58/1.48  --pure_diseq_elim                       true
% 7.58/1.48  --brand_transform                       false
% 7.58/1.48  --non_eq_to_eq                          false
% 7.58/1.48  --prep_def_merge                        true
% 7.58/1.48  --prep_def_merge_prop_impl              false
% 7.58/1.48  --prep_def_merge_mbd                    true
% 7.58/1.48  --prep_def_merge_tr_red                 false
% 7.58/1.48  --prep_def_merge_tr_cl                  false
% 7.58/1.48  --smt_preprocessing                     true
% 7.58/1.48  --smt_ac_axioms                         fast
% 7.58/1.48  --preprocessed_out                      false
% 7.58/1.48  --preprocessed_stats                    false
% 7.58/1.48  
% 7.58/1.48  ------ Abstraction refinement Options
% 7.58/1.48  
% 7.58/1.48  --abstr_ref                             []
% 7.58/1.48  --abstr_ref_prep                        false
% 7.58/1.48  --abstr_ref_until_sat                   false
% 7.58/1.48  --abstr_ref_sig_restrict                funpre
% 7.58/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.48  --abstr_ref_under                       []
% 7.58/1.48  
% 7.58/1.48  ------ SAT Options
% 7.58/1.48  
% 7.58/1.48  --sat_mode                              false
% 7.58/1.48  --sat_fm_restart_options                ""
% 7.58/1.48  --sat_gr_def                            false
% 7.58/1.48  --sat_epr_types                         true
% 7.58/1.48  --sat_non_cyclic_types                  false
% 7.58/1.48  --sat_finite_models                     false
% 7.58/1.48  --sat_fm_lemmas                         false
% 7.58/1.48  --sat_fm_prep                           false
% 7.58/1.48  --sat_fm_uc_incr                        true
% 7.58/1.48  --sat_out_model                         small
% 7.58/1.48  --sat_out_clauses                       false
% 7.58/1.48  
% 7.58/1.48  ------ QBF Options
% 7.58/1.48  
% 7.58/1.48  --qbf_mode                              false
% 7.58/1.48  --qbf_elim_univ                         false
% 7.58/1.48  --qbf_dom_inst                          none
% 7.58/1.48  --qbf_dom_pre_inst                      false
% 7.58/1.48  --qbf_sk_in                             false
% 7.58/1.48  --qbf_pred_elim                         true
% 7.58/1.48  --qbf_split                             512
% 7.58/1.48  
% 7.58/1.48  ------ BMC1 Options
% 7.58/1.48  
% 7.58/1.48  --bmc1_incremental                      false
% 7.58/1.48  --bmc1_axioms                           reachable_all
% 7.58/1.48  --bmc1_min_bound                        0
% 7.58/1.48  --bmc1_max_bound                        -1
% 7.58/1.48  --bmc1_max_bound_default                -1
% 7.58/1.48  --bmc1_symbol_reachability              true
% 7.58/1.48  --bmc1_property_lemmas                  false
% 7.58/1.48  --bmc1_k_induction                      false
% 7.58/1.48  --bmc1_non_equiv_states                 false
% 7.58/1.48  --bmc1_deadlock                         false
% 7.58/1.48  --bmc1_ucm                              false
% 7.58/1.48  --bmc1_add_unsat_core                   none
% 7.58/1.48  --bmc1_unsat_core_children              false
% 7.58/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.48  --bmc1_out_stat                         full
% 7.58/1.48  --bmc1_ground_init                      false
% 7.58/1.48  --bmc1_pre_inst_next_state              false
% 7.58/1.48  --bmc1_pre_inst_state                   false
% 7.58/1.48  --bmc1_pre_inst_reach_state             false
% 7.58/1.48  --bmc1_out_unsat_core                   false
% 7.58/1.48  --bmc1_aig_witness_out                  false
% 7.58/1.48  --bmc1_verbose                          false
% 7.58/1.48  --bmc1_dump_clauses_tptp                false
% 7.58/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.48  --bmc1_dump_file                        -
% 7.58/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.48  --bmc1_ucm_extend_mode                  1
% 7.58/1.48  --bmc1_ucm_init_mode                    2
% 7.58/1.48  --bmc1_ucm_cone_mode                    none
% 7.58/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.48  --bmc1_ucm_relax_model                  4
% 7.58/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.48  --bmc1_ucm_layered_model                none
% 7.58/1.48  --bmc1_ucm_max_lemma_size               10
% 7.58/1.48  
% 7.58/1.48  ------ AIG Options
% 7.58/1.48  
% 7.58/1.48  --aig_mode                              false
% 7.58/1.48  
% 7.58/1.48  ------ Instantiation Options
% 7.58/1.48  
% 7.58/1.48  --instantiation_flag                    true
% 7.58/1.48  --inst_sos_flag                         true
% 7.58/1.48  --inst_sos_phase                        true
% 7.58/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.48  --inst_lit_sel_side                     none
% 7.58/1.48  --inst_solver_per_active                1400
% 7.58/1.48  --inst_solver_calls_frac                1.
% 7.58/1.48  --inst_passive_queue_type               priority_queues
% 7.58/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.48  --inst_passive_queues_freq              [25;2]
% 7.58/1.48  --inst_dismatching                      true
% 7.58/1.48  --inst_eager_unprocessed_to_passive     true
% 7.58/1.48  --inst_prop_sim_given                   true
% 7.58/1.48  --inst_prop_sim_new                     false
% 7.58/1.48  --inst_subs_new                         false
% 7.58/1.48  --inst_eq_res_simp                      false
% 7.58/1.48  --inst_subs_given                       false
% 7.58/1.48  --inst_orphan_elimination               true
% 7.58/1.48  --inst_learning_loop_flag               true
% 7.58/1.48  --inst_learning_start                   3000
% 7.58/1.48  --inst_learning_factor                  2
% 7.58/1.48  --inst_start_prop_sim_after_learn       3
% 7.58/1.48  --inst_sel_renew                        solver
% 7.58/1.48  --inst_lit_activity_flag                true
% 7.58/1.48  --inst_restr_to_given                   false
% 7.58/1.48  --inst_activity_threshold               500
% 7.58/1.48  --inst_out_proof                        true
% 7.58/1.48  
% 7.58/1.48  ------ Resolution Options
% 7.58/1.48  
% 7.58/1.48  --resolution_flag                       false
% 7.58/1.48  --res_lit_sel                           adaptive
% 7.58/1.48  --res_lit_sel_side                      none
% 7.58/1.48  --res_ordering                          kbo
% 7.58/1.48  --res_to_prop_solver                    active
% 7.58/1.48  --res_prop_simpl_new                    false
% 7.58/1.48  --res_prop_simpl_given                  true
% 7.58/1.48  --res_passive_queue_type                priority_queues
% 7.58/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.48  --res_passive_queues_freq               [15;5]
% 7.58/1.48  --res_forward_subs                      full
% 7.58/1.48  --res_backward_subs                     full
% 7.58/1.48  --res_forward_subs_resolution           true
% 7.58/1.48  --res_backward_subs_resolution          true
% 7.58/1.48  --res_orphan_elimination                true
% 7.58/1.48  --res_time_limit                        2.
% 7.58/1.48  --res_out_proof                         true
% 7.58/1.48  
% 7.58/1.48  ------ Superposition Options
% 7.58/1.48  
% 7.58/1.48  --superposition_flag                    true
% 7.58/1.48  --sup_passive_queue_type                priority_queues
% 7.58/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.48  --demod_completeness_check              fast
% 7.58/1.48  --demod_use_ground                      true
% 7.58/1.48  --sup_to_prop_solver                    passive
% 7.58/1.48  --sup_prop_simpl_new                    true
% 7.58/1.48  --sup_prop_simpl_given                  true
% 7.58/1.48  --sup_fun_splitting                     true
% 7.58/1.48  --sup_smt_interval                      50000
% 7.58/1.48  
% 7.58/1.48  ------ Superposition Simplification Setup
% 7.58/1.48  
% 7.58/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.58/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.58/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.58/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.58/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.58/1.48  --sup_immed_triv                        [TrivRules]
% 7.58/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.48  --sup_immed_bw_main                     []
% 7.58/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.58/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.48  --sup_input_bw                          []
% 7.58/1.48  
% 7.58/1.48  ------ Combination Options
% 7.58/1.48  
% 7.58/1.48  --comb_res_mult                         3
% 7.58/1.48  --comb_sup_mult                         2
% 7.58/1.48  --comb_inst_mult                        10
% 7.58/1.48  
% 7.58/1.48  ------ Debug Options
% 7.58/1.48  
% 7.58/1.48  --dbg_backtrace                         false
% 7.58/1.48  --dbg_dump_prop_clauses                 false
% 7.58/1.48  --dbg_dump_prop_clauses_file            -
% 7.58/1.48  --dbg_out_stat                          false
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  ------ Proving...
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  % SZS status Theorem for theBenchmark.p
% 7.58/1.48  
% 7.58/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.48  
% 7.58/1.48  fof(f11,axiom,(
% 7.58/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 7.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f29,plain,(
% 7.58/1.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.58/1.48    inference(ennf_transformation,[],[f11])).
% 7.58/1.48  
% 7.58/1.48  fof(f30,plain,(
% 7.58/1.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.48    inference(flattening,[],[f29])).
% 7.58/1.48  
% 7.58/1.48  fof(f65,plain,(
% 7.58/1.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.48    inference(nnf_transformation,[],[f30])).
% 7.58/1.48  
% 7.58/1.48  fof(f66,plain,(
% 7.58/1.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.48    inference(rectify,[],[f65])).
% 7.58/1.48  
% 7.58/1.48  fof(f69,plain,(
% 7.58/1.48    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1,X6)) = X6 & r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))))),
% 7.58/1.48    introduced(choice_axiom,[])).
% 7.58/1.48  
% 7.58/1.48  fof(f68,plain,(
% 7.58/1.48    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0))))) )),
% 7.58/1.48    introduced(choice_axiom,[])).
% 7.58/1.48  
% 7.58/1.48  fof(f67,plain,(
% 7.58/1.48    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK3(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 7.58/1.48    introduced(choice_axiom,[])).
% 7.58/1.48  
% 7.58/1.48  fof(f70,plain,(
% 7.58/1.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK4(X0,X1,X2)) = sK3(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X1,X6)) = X6 & r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f66,f69,f68,f67])).
% 7.58/1.48  
% 7.58/1.48  fof(f108,plain,(
% 7.58/1.48    ( ! [X6,X2,X0,X1] : (r2_hidden(sK5(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f70])).
% 7.58/1.48  
% 7.58/1.48  fof(f150,plain,(
% 7.58/1.48    ( ! [X6,X0,X1] : (r2_hidden(sK5(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.48    inference(equality_resolution,[],[f108])).
% 7.58/1.48  
% 7.58/1.48  fof(f20,axiom,(
% 7.58/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f41,plain,(
% 7.58/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.48    inference(ennf_transformation,[],[f20])).
% 7.58/1.48  
% 7.58/1.48  fof(f42,plain,(
% 7.58/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.48    inference(flattening,[],[f41])).
% 7.58/1.48  
% 7.58/1.48  fof(f81,plain,(
% 7.58/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.48    inference(nnf_transformation,[],[f42])).
% 7.58/1.48  
% 7.58/1.48  fof(f131,plain,(
% 7.58/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.48    inference(cnf_transformation,[],[f81])).
% 7.58/1.48  
% 7.58/1.48  fof(f22,conjecture,(
% 7.58/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f23,negated_conjecture,(
% 7.58/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.58/1.48    inference(negated_conjecture,[],[f22])).
% 7.58/1.48  
% 7.58/1.48  fof(f45,plain,(
% 7.58/1.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.58/1.48    inference(ennf_transformation,[],[f23])).
% 7.58/1.48  
% 7.58/1.48  fof(f46,plain,(
% 7.58/1.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.58/1.48    inference(flattening,[],[f45])).
% 7.58/1.48  
% 7.58/1.48  fof(f83,plain,(
% 7.58/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK16 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK16,k7_relset_1(X0,X1,X3,X2)))) )),
% 7.58/1.48    introduced(choice_axiom,[])).
% 7.58/1.48  
% 7.58/1.48  fof(f82,plain,(
% 7.58/1.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK15,X5) != X4 | ~r2_hidden(X5,sK14) | ~m1_subset_1(X5,sK12)) & r2_hidden(X4,k7_relset_1(sK12,sK13,sK15,sK14))) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13))) & v1_funct_2(sK15,sK12,sK13) & v1_funct_1(sK15))),
% 7.58/1.48    introduced(choice_axiom,[])).
% 7.58/1.48  
% 7.58/1.48  fof(f84,plain,(
% 7.58/1.48    (! [X5] : (k1_funct_1(sK15,X5) != sK16 | ~r2_hidden(X5,sK14) | ~m1_subset_1(X5,sK12)) & r2_hidden(sK16,k7_relset_1(sK12,sK13,sK15,sK14))) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13))) & v1_funct_2(sK15,sK12,sK13) & v1_funct_1(sK15)),
% 7.58/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14,sK15,sK16])],[f46,f83,f82])).
% 7.58/1.48  
% 7.58/1.48  fof(f141,plain,(
% 7.58/1.48    v1_funct_2(sK15,sK12,sK13)),
% 7.58/1.48    inference(cnf_transformation,[],[f84])).
% 7.58/1.48  
% 7.58/1.48  fof(f142,plain,(
% 7.58/1.48    m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13)))),
% 7.58/1.48    inference(cnf_transformation,[],[f84])).
% 7.58/1.48  
% 7.58/1.48  fof(f18,axiom,(
% 7.58/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.58/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f39,plain,(
% 7.58/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.48    inference(ennf_transformation,[],[f18])).
% 7.58/1.48  
% 7.58/1.48  fof(f129,plain,(
% 7.58/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.48    inference(cnf_transformation,[],[f39])).
% 7.58/1.48  
% 7.58/1.48  fof(f107,plain,(
% 7.58/1.48    ( ! [X6,X2,X0,X1] : (r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f70])).
% 7.58/1.48  
% 7.58/1.48  fof(f151,plain,(
% 7.58/1.48    ( ! [X6,X0,X1] : (r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.49    inference(equality_resolution,[],[f107])).
% 7.58/1.49  
% 7.58/1.49  fof(f140,plain,(
% 7.58/1.49    v1_funct_1(sK15)),
% 7.58/1.49    inference(cnf_transformation,[],[f84])).
% 7.58/1.49  
% 7.58/1.49  fof(f15,axiom,(
% 7.58/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f36,plain,(
% 7.58/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.49    inference(ennf_transformation,[],[f15])).
% 7.58/1.49  
% 7.58/1.49  fof(f126,plain,(
% 7.58/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.49    inference(cnf_transformation,[],[f36])).
% 7.58/1.49  
% 7.58/1.49  fof(f6,axiom,(
% 7.58/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f26,plain,(
% 7.58/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.58/1.49    inference(ennf_transformation,[],[f6])).
% 7.58/1.49  
% 7.58/1.49  fof(f97,plain,(
% 7.58/1.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f26])).
% 7.58/1.49  
% 7.58/1.49  fof(f19,axiom,(
% 7.58/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f40,plain,(
% 7.58/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.49    inference(ennf_transformation,[],[f19])).
% 7.58/1.49  
% 7.58/1.49  fof(f130,plain,(
% 7.58/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.49    inference(cnf_transformation,[],[f40])).
% 7.58/1.49  
% 7.58/1.49  fof(f143,plain,(
% 7.58/1.49    r2_hidden(sK16,k7_relset_1(sK12,sK13,sK15,sK14))),
% 7.58/1.49    inference(cnf_transformation,[],[f84])).
% 7.58/1.49  
% 7.58/1.49  fof(f109,plain,(
% 7.58/1.49    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK5(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f70])).
% 7.58/1.49  
% 7.58/1.49  fof(f149,plain,(
% 7.58/1.49    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK5(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.49    inference(equality_resolution,[],[f109])).
% 7.58/1.49  
% 7.58/1.49  fof(f144,plain,(
% 7.58/1.49    ( ! [X5] : (k1_funct_1(sK15,X5) != sK16 | ~r2_hidden(X5,sK14) | ~m1_subset_1(X5,sK12)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f84])).
% 7.58/1.49  
% 7.58/1.49  fof(f12,axiom,(
% 7.58/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f31,plain,(
% 7.58/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.58/1.49    inference(ennf_transformation,[],[f12])).
% 7.58/1.49  
% 7.58/1.49  fof(f32,plain,(
% 7.58/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.49    inference(flattening,[],[f31])).
% 7.58/1.49  
% 7.58/1.49  fof(f71,plain,(
% 7.58/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.49    inference(nnf_transformation,[],[f32])).
% 7.58/1.49  
% 7.58/1.49  fof(f72,plain,(
% 7.58/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.49    inference(rectify,[],[f71])).
% 7.58/1.49  
% 7.58/1.49  fof(f75,plain,(
% 7.58/1.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))))),
% 7.58/1.49    introduced(choice_axiom,[])).
% 7.58/1.49  
% 7.58/1.49  fof(f74,plain,(
% 7.58/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1)) = X2 & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))) )),
% 7.58/1.49    introduced(choice_axiom,[])).
% 7.58/1.49  
% 7.58/1.49  fof(f73,plain,(
% 7.58/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1))))),
% 7.58/1.49    introduced(choice_axiom,[])).
% 7.58/1.49  
% 7.58/1.49  fof(f76,plain,(
% 7.58/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & ((k1_funct_1(X0,sK7(X0,X1)) = sK6(X0,X1) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f72,f75,f74,f73])).
% 7.58/1.49  
% 7.58/1.49  fof(f117,plain,(
% 7.58/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f76])).
% 7.58/1.49  
% 7.58/1.49  fof(f152,plain,(
% 7.58/1.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.49    inference(equality_resolution,[],[f117])).
% 7.58/1.49  
% 7.58/1.49  fof(f153,plain,(
% 7.58/1.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.49    inference(equality_resolution,[],[f152])).
% 7.58/1.49  
% 7.58/1.49  fof(f16,axiom,(
% 7.58/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f24,plain,(
% 7.58/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.58/1.49    inference(pure_predicate_removal,[],[f16])).
% 7.58/1.49  
% 7.58/1.49  fof(f37,plain,(
% 7.58/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.49    inference(ennf_transformation,[],[f24])).
% 7.58/1.49  
% 7.58/1.49  fof(f127,plain,(
% 7.58/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.49    inference(cnf_transformation,[],[f37])).
% 7.58/1.49  
% 7.58/1.49  fof(f8,axiom,(
% 7.58/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f27,plain,(
% 7.58/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.58/1.49    inference(ennf_transformation,[],[f8])).
% 7.58/1.49  
% 7.58/1.49  fof(f60,plain,(
% 7.58/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.58/1.49    inference(nnf_transformation,[],[f27])).
% 7.58/1.49  
% 7.58/1.49  fof(f100,plain,(
% 7.58/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f60])).
% 7.58/1.49  
% 7.58/1.49  fof(f2,axiom,(
% 7.58/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f25,plain,(
% 7.58/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.58/1.49    inference(ennf_transformation,[],[f2])).
% 7.58/1.49  
% 7.58/1.49  fof(f51,plain,(
% 7.58/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.58/1.49    inference(nnf_transformation,[],[f25])).
% 7.58/1.49  
% 7.58/1.49  fof(f52,plain,(
% 7.58/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.58/1.49    inference(rectify,[],[f51])).
% 7.58/1.49  
% 7.58/1.49  fof(f53,plain,(
% 7.58/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.58/1.49    introduced(choice_axiom,[])).
% 7.58/1.49  
% 7.58/1.49  fof(f54,plain,(
% 7.58/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.58/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 7.58/1.49  
% 7.58/1.49  fof(f87,plain,(
% 7.58/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f54])).
% 7.58/1.49  
% 7.58/1.49  fof(f1,axiom,(
% 7.58/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f47,plain,(
% 7.58/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.58/1.49    inference(nnf_transformation,[],[f1])).
% 7.58/1.49  
% 7.58/1.49  fof(f48,plain,(
% 7.58/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.58/1.49    inference(rectify,[],[f47])).
% 7.58/1.49  
% 7.58/1.49  fof(f49,plain,(
% 7.58/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.58/1.49    introduced(choice_axiom,[])).
% 7.58/1.49  
% 7.58/1.49  fof(f50,plain,(
% 7.58/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.58/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 7.58/1.49  
% 7.58/1.49  fof(f85,plain,(
% 7.58/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f50])).
% 7.58/1.49  
% 7.58/1.49  fof(f86,plain,(
% 7.58/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f50])).
% 7.58/1.49  
% 7.58/1.49  fof(f4,axiom,(
% 7.58/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f93,plain,(
% 7.58/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f4])).
% 7.58/1.49  
% 7.58/1.49  fof(f14,axiom,(
% 7.58/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.58/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.49  
% 7.58/1.49  fof(f35,plain,(
% 7.58/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.58/1.49    inference(ennf_transformation,[],[f14])).
% 7.58/1.49  
% 7.58/1.49  fof(f125,plain,(
% 7.58/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.58/1.49    inference(cnf_transformation,[],[f35])).
% 7.58/1.49  
% 7.58/1.49  cnf(c_28,plain,
% 7.58/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.58/1.49      | r2_hidden(sK5(X1,X2,X0),X2)
% 7.58/1.49      | ~ v1_funct_1(X1)
% 7.58/1.49      | ~ v1_relat_1(X1) ),
% 7.58/1.49      inference(cnf_transformation,[],[f150]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9132,plain,
% 7.58/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.58/1.49      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top
% 7.58/1.49      | v1_funct_1(X1) != iProver_top
% 7.58/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_51,plain,
% 7.58/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.58/1.49      | k1_xboole_0 = X2 ),
% 7.58/1.49      inference(cnf_transformation,[],[f131]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_58,negated_conjecture,
% 7.58/1.49      ( v1_funct_2(sK15,sK12,sK13) ),
% 7.58/1.49      inference(cnf_transformation,[],[f141]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_913,plain,
% 7.58/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.58/1.49      | sK13 != X2
% 7.58/1.49      | sK12 != X1
% 7.58/1.49      | sK15 != X0
% 7.58/1.49      | k1_xboole_0 = X2 ),
% 7.58/1.49      inference(resolution_lifted,[status(thm)],[c_51,c_58]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_914,plain,
% 7.58/1.49      ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13)))
% 7.58/1.49      | k1_relset_1(sK12,sK13,sK15) = sK12
% 7.58/1.49      | k1_xboole_0 = sK13 ),
% 7.58/1.49      inference(unflattening,[status(thm)],[c_913]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_57,negated_conjecture,
% 7.58/1.49      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13))) ),
% 7.58/1.49      inference(cnf_transformation,[],[f142]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_916,plain,
% 7.58/1.49      ( k1_relset_1(sK12,sK13,sK15) = sK12 | k1_xboole_0 = sK13 ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_914,c_57]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9112,plain,
% 7.58/1.49      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK12,sK13))) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_44,plain,
% 7.58/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.58/1.49      inference(cnf_transformation,[],[f129]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9117,plain,
% 7.58/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.58/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_12418,plain,
% 7.58/1.49      ( k1_relset_1(sK12,sK13,sK15) = k1_relat_1(sK15) ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_9112,c_9117]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_12524,plain,
% 7.58/1.49      ( k1_relat_1(sK15) = sK12 | sK13 = k1_xboole_0 ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_916,c_12418]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_29,plain,
% 7.58/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.58/1.49      | r2_hidden(sK5(X1,X2,X0),k1_relat_1(X1))
% 7.58/1.49      | ~ v1_funct_1(X1)
% 7.58/1.49      | ~ v1_relat_1(X1) ),
% 7.58/1.49      inference(cnf_transformation,[],[f151]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9131,plain,
% 7.58/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.58/1.49      | r2_hidden(sK5(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 7.58/1.49      | v1_funct_1(X1) != iProver_top
% 7.58/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_14981,plain,
% 7.58/1.49      ( sK13 = k1_xboole_0
% 7.58/1.49      | r2_hidden(X0,k9_relat_1(sK15,X1)) != iProver_top
% 7.58/1.49      | r2_hidden(sK5(sK15,X1,X0),sK12) = iProver_top
% 7.58/1.49      | v1_funct_1(sK15) != iProver_top
% 7.58/1.49      | v1_relat_1(sK15) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_12524,c_9131]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_59,negated_conjecture,
% 7.58/1.49      ( v1_funct_1(sK15) ),
% 7.58/1.49      inference(cnf_transformation,[],[f140]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_60,plain,
% 7.58/1.49      ( v1_funct_1(sK15) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_41,plain,
% 7.58/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.49      | v1_relat_1(X0) ),
% 7.58/1.49      inference(cnf_transformation,[],[f126]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9119,plain,
% 7.58/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.58/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_10774,plain,
% 7.58/1.49      ( v1_relat_1(sK15) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_9112,c_9119]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_15381,plain,
% 7.58/1.49      ( sK13 = k1_xboole_0
% 7.58/1.49      | r2_hidden(X0,k9_relat_1(sK15,X1)) != iProver_top
% 7.58/1.49      | r2_hidden(sK5(sK15,X1,X0),sK12) = iProver_top ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_14981,c_60,c_10774]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_12,plain,
% 7.58/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.58/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9146,plain,
% 7.58/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.58/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_15388,plain,
% 7.58/1.49      ( sK13 = k1_xboole_0
% 7.58/1.49      | m1_subset_1(sK5(sK15,X0,X1),sK12) = iProver_top
% 7.58/1.49      | r2_hidden(X1,k9_relat_1(sK15,X0)) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_15381,c_9146]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_45,plain,
% 7.58/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.58/1.49      inference(cnf_transformation,[],[f130]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9116,plain,
% 7.58/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.58/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_12516,plain,
% 7.58/1.49      ( k7_relset_1(sK12,sK13,sK15,X0) = k9_relat_1(sK15,X0) ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_9112,c_9116]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_56,negated_conjecture,
% 7.58/1.49      ( r2_hidden(sK16,k7_relset_1(sK12,sK13,sK15,sK14)) ),
% 7.58/1.49      inference(cnf_transformation,[],[f143]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9113,plain,
% 7.58/1.49      ( r2_hidden(sK16,k7_relset_1(sK12,sK13,sK15,sK14)) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_12622,plain,
% 7.58/1.49      ( r2_hidden(sK16,k9_relat_1(sK15,sK14)) = iProver_top ),
% 7.58/1.49      inference(demodulation,[status(thm)],[c_12516,c_9113]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_27,plain,
% 7.58/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.58/1.49      | ~ v1_funct_1(X1)
% 7.58/1.49      | ~ v1_relat_1(X1)
% 7.58/1.49      | k1_funct_1(X1,sK5(X1,X2,X0)) = X0 ),
% 7.58/1.49      inference(cnf_transformation,[],[f149]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9133,plain,
% 7.58/1.49      ( k1_funct_1(X0,sK5(X0,X1,X2)) = X2
% 7.58/1.49      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 7.58/1.49      | v1_funct_1(X0) != iProver_top
% 7.58/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_14906,plain,
% 7.58/1.49      ( k1_funct_1(sK15,sK5(sK15,sK14,sK16)) = sK16
% 7.58/1.49      | v1_funct_1(sK15) != iProver_top
% 7.58/1.49      | v1_relat_1(sK15) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_12622,c_9133]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_15227,plain,
% 7.58/1.49      ( k1_funct_1(sK15,sK5(sK15,sK14,sK16)) = sK16 ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_14906,c_60,c_10774]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_55,negated_conjecture,
% 7.58/1.49      ( ~ m1_subset_1(X0,sK12)
% 7.58/1.49      | ~ r2_hidden(X0,sK14)
% 7.58/1.49      | k1_funct_1(sK15,X0) != sK16 ),
% 7.58/1.49      inference(cnf_transformation,[],[f144]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9114,plain,
% 7.58/1.49      ( k1_funct_1(sK15,X0) != sK16
% 7.58/1.49      | m1_subset_1(X0,sK12) != iProver_top
% 7.58/1.49      | r2_hidden(X0,sK14) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_15230,plain,
% 7.58/1.49      ( m1_subset_1(sK5(sK15,sK14,sK16),sK12) != iProver_top
% 7.58/1.49      | r2_hidden(sK5(sK15,sK14,sK16),sK14) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_15227,c_9114]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_25184,plain,
% 7.58/1.49      ( sK13 = k1_xboole_0
% 7.58/1.49      | r2_hidden(sK5(sK15,sK14,sK16),sK14) != iProver_top
% 7.58/1.49      | r2_hidden(sK16,k9_relat_1(sK15,sK14)) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_15388,c_15230]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_25845,plain,
% 7.58/1.49      ( r2_hidden(sK5(sK15,sK14,sK16),sK14) != iProver_top
% 7.58/1.49      | sK13 = k1_xboole_0 ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_25184,c_12622]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_25846,plain,
% 7.58/1.49      ( sK13 = k1_xboole_0
% 7.58/1.49      | r2_hidden(sK5(sK15,sK14,sK16),sK14) != iProver_top ),
% 7.58/1.49      inference(renaming,[status(thm)],[c_25845]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_25849,plain,
% 7.58/1.49      ( sK13 = k1_xboole_0
% 7.58/1.49      | r2_hidden(sK16,k9_relat_1(sK15,sK14)) != iProver_top
% 7.58/1.49      | v1_funct_1(sK15) != iProver_top
% 7.58/1.49      | v1_relat_1(sK15) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_9132,c_25846]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_27416,plain,
% 7.58/1.49      ( sK13 = k1_xboole_0 ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_25849,c_60,c_10774,c_12622]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_33,plain,
% 7.58/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.58/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.58/1.49      | ~ v1_funct_1(X1)
% 7.58/1.49      | ~ v1_relat_1(X1) ),
% 7.58/1.49      inference(cnf_transformation,[],[f153]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9127,plain,
% 7.58/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.58/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 7.58/1.49      | v1_funct_1(X1) != iProver_top
% 7.58/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_42,plain,
% 7.58/1.49      ( v5_relat_1(X0,X1)
% 7.58/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.58/1.49      inference(cnf_transformation,[],[f127]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_16,plain,
% 7.58/1.49      ( ~ v5_relat_1(X0,X1)
% 7.58/1.49      | r1_tarski(k2_relat_1(X0),X1)
% 7.58/1.49      | ~ v1_relat_1(X0) ),
% 7.58/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_769,plain,
% 7.58/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.49      | r1_tarski(k2_relat_1(X0),X2)
% 7.58/1.49      | ~ v1_relat_1(X0) ),
% 7.58/1.49      inference(resolution,[status(thm)],[c_42,c_16]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_773,plain,
% 7.58/1.49      ( r1_tarski(k2_relat_1(X0),X2)
% 7.58/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_769,c_41]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_774,plain,
% 7.58/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.49      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.58/1.49      inference(renaming,[status(thm)],[c_773]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9110,plain,
% 7.58/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.58/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_11996,plain,
% 7.58/1.49      ( r1_tarski(k2_relat_1(sK15),sK13) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_9112,c_9110]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_4,plain,
% 7.58/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.58/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9153,plain,
% 7.58/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.58/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_13331,plain,
% 7.58/1.49      ( r2_hidden(X0,k2_relat_1(sK15)) != iProver_top
% 7.58/1.49      | r2_hidden(X0,sK13) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_11996,c_9153]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_14138,plain,
% 7.58/1.49      ( r2_hidden(X0,k1_relat_1(sK15)) != iProver_top
% 7.58/1.49      | r2_hidden(k1_funct_1(sK15,X0),sK13) = iProver_top
% 7.58/1.49      | v1_funct_1(sK15) != iProver_top
% 7.58/1.49      | v1_relat_1(sK15) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_9127,c_13331]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_15807,plain,
% 7.58/1.49      ( r2_hidden(X0,k1_relat_1(sK15)) != iProver_top
% 7.58/1.49      | r2_hidden(k1_funct_1(sK15,X0),sK13) = iProver_top ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_14138,c_60,c_10774]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_15813,plain,
% 7.58/1.49      ( r2_hidden(sK5(sK15,sK14,sK16),k1_relat_1(sK15)) != iProver_top
% 7.58/1.49      | r2_hidden(sK16,sK13) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_15227,c_15807]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_15825,plain,
% 7.58/1.49      ( sK13 = k1_xboole_0
% 7.58/1.49      | r2_hidden(sK5(sK15,sK14,sK16),sK12) != iProver_top
% 7.58/1.49      | r2_hidden(sK16,sK13) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_12524,c_15813]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_15824,plain,
% 7.58/1.49      ( r2_hidden(sK16,k9_relat_1(sK15,sK14)) != iProver_top
% 7.58/1.49      | r2_hidden(sK16,sK13) = iProver_top
% 7.58/1.49      | v1_funct_1(sK15) != iProver_top
% 7.58/1.49      | v1_relat_1(sK15) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_9131,c_15813]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_16447,plain,
% 7.58/1.49      ( r2_hidden(sK16,sK13) = iProver_top ),
% 7.58/1.49      inference(global_propositional_subsumption,
% 7.58/1.49                [status(thm)],
% 7.58/1.49                [c_15825,c_60,c_10774,c_12622,c_15824]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_1,plain,
% 7.58/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.58/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9156,plain,
% 7.58/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.58/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_16451,plain,
% 7.58/1.49      ( v1_xboole_0(sK13) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_16447,c_9156]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_27433,plain,
% 7.58/1.49      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.58/1.49      inference(demodulation,[status(thm)],[c_27416,c_16451]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_0,plain,
% 7.58/1.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.58/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9157,plain,
% 7.58/1.49      ( r2_hidden(sK0(X0),X0) = iProver_top
% 7.58/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_8,plain,
% 7.58/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.58/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9150,plain,
% 7.58/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_40,plain,
% 7.58/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 7.58/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_9120,plain,
% 7.58/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.58/1.49      | r2_hidden(X1,X0) != iProver_top ),
% 7.58/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_10340,plain,
% 7.58/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_9150,c_9120]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(c_10440,plain,
% 7.58/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.58/1.49      inference(superposition,[status(thm)],[c_9157,c_10340]) ).
% 7.58/1.49  
% 7.58/1.49  cnf(contradiction,plain,
% 7.58/1.49      ( $false ),
% 7.58/1.49      inference(minisat,[status(thm)],[c_27433,c_10440]) ).
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.49  
% 7.58/1.49  ------                               Statistics
% 7.58/1.49  
% 7.58/1.49  ------ General
% 7.58/1.49  
% 7.58/1.49  abstr_ref_over_cycles:                  0
% 7.58/1.49  abstr_ref_under_cycles:                 0
% 7.58/1.49  gc_basic_clause_elim:                   0
% 7.58/1.49  forced_gc_time:                         0
% 7.58/1.49  parsing_time:                           0.01
% 7.58/1.49  unif_index_cands_time:                  0.
% 7.58/1.49  unif_index_add_time:                    0.
% 7.58/1.49  orderings_time:                         0.
% 7.58/1.49  out_proof_time:                         0.015
% 7.58/1.49  total_time:                             0.669
% 7.58/1.49  num_of_symbols:                         66
% 7.58/1.49  num_of_terms:                           26911
% 7.58/1.49  
% 7.58/1.49  ------ Preprocessing
% 7.58/1.49  
% 7.58/1.49  num_of_splits:                          0
% 7.58/1.49  num_of_split_atoms:                     0
% 7.58/1.49  num_of_reused_defs:                     0
% 7.58/1.49  num_eq_ax_congr_red:                    92
% 7.58/1.49  num_of_sem_filtered_clauses:            1
% 7.58/1.49  num_of_subtypes:                        0
% 7.58/1.49  monotx_restored_types:                  0
% 7.58/1.49  sat_num_of_epr_types:                   0
% 7.58/1.49  sat_num_of_non_cyclic_types:            0
% 7.58/1.49  sat_guarded_non_collapsed_types:        0
% 7.58/1.49  num_pure_diseq_elim:                    0
% 7.58/1.49  simp_replaced_by:                       0
% 7.58/1.49  res_preprocessed:                       247
% 7.58/1.49  prep_upred:                             0
% 7.58/1.49  prep_unflattend:                        295
% 7.58/1.49  smt_new_axioms:                         0
% 7.58/1.49  pred_elim_cands:                        6
% 7.58/1.49  pred_elim:                              2
% 7.58/1.49  pred_elim_cl:                           4
% 7.58/1.49  pred_elim_cycles:                       8
% 7.58/1.49  merged_defs:                            8
% 7.58/1.49  merged_defs_ncl:                        0
% 7.58/1.49  bin_hyper_res:                          8
% 7.58/1.49  prep_cycles:                            4
% 7.58/1.49  pred_elim_time:                         0.115
% 7.58/1.49  splitting_time:                         0.
% 7.58/1.49  sem_filter_time:                        0.
% 7.58/1.49  monotx_time:                            0.
% 7.58/1.49  subtype_inf_time:                       0.
% 7.58/1.49  
% 7.58/1.49  ------ Problem properties
% 7.58/1.49  
% 7.58/1.49  clauses:                                54
% 7.58/1.49  conjectures:                            4
% 7.58/1.49  epr:                                    8
% 7.58/1.49  horn:                                   41
% 7.58/1.49  ground:                                 6
% 7.58/1.49  unary:                                  6
% 7.58/1.49  binary:                                 18
% 7.58/1.49  lits:                                   167
% 7.58/1.49  lits_eq:                                32
% 7.58/1.49  fd_pure:                                0
% 7.58/1.49  fd_pseudo:                              0
% 7.58/1.49  fd_cond:                                2
% 7.58/1.49  fd_pseudo_cond:                         9
% 7.58/1.49  ac_symbols:                             0
% 7.58/1.49  
% 7.58/1.49  ------ Propositional Solver
% 7.58/1.49  
% 7.58/1.49  prop_solver_calls:                      31
% 7.58/1.49  prop_fast_solver_calls:                 3397
% 7.58/1.49  smt_solver_calls:                       0
% 7.58/1.49  smt_fast_solver_calls:                  0
% 7.58/1.49  prop_num_of_clauses:                    11055
% 7.58/1.49  prop_preprocess_simplified:             28209
% 7.58/1.49  prop_fo_subsumed:                       55
% 7.58/1.49  prop_solver_time:                       0.
% 7.58/1.49  smt_solver_time:                        0.
% 7.58/1.49  smt_fast_solver_time:                   0.
% 7.58/1.49  prop_fast_solver_time:                  0.
% 7.58/1.49  prop_unsat_core_time:                   0.001
% 7.58/1.49  
% 7.58/1.49  ------ QBF
% 7.58/1.49  
% 7.58/1.49  qbf_q_res:                              0
% 7.58/1.49  qbf_num_tautologies:                    0
% 7.58/1.49  qbf_prep_cycles:                        0
% 7.58/1.49  
% 7.58/1.49  ------ BMC1
% 7.58/1.49  
% 7.58/1.49  bmc1_current_bound:                     -1
% 7.58/1.49  bmc1_last_solved_bound:                 -1
% 7.58/1.49  bmc1_unsat_core_size:                   -1
% 7.58/1.49  bmc1_unsat_core_parents_size:           -1
% 7.58/1.49  bmc1_merge_next_fun:                    0
% 7.58/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.58/1.49  
% 7.58/1.49  ------ Instantiation
% 7.58/1.49  
% 7.58/1.49  inst_num_of_clauses:                    2651
% 7.58/1.49  inst_num_in_passive:                    1905
% 7.58/1.49  inst_num_in_active:                     680
% 7.58/1.49  inst_num_in_unprocessed:                66
% 7.58/1.49  inst_num_of_loops:                      830
% 7.58/1.49  inst_num_of_learning_restarts:          0
% 7.58/1.49  inst_num_moves_active_passive:          150
% 7.58/1.49  inst_lit_activity:                      0
% 7.58/1.49  inst_lit_activity_moves:                0
% 7.58/1.49  inst_num_tautologies:                   0
% 7.58/1.49  inst_num_prop_implied:                  0
% 7.58/1.49  inst_num_existing_simplified:           0
% 7.58/1.49  inst_num_eq_res_simplified:             0
% 7.58/1.49  inst_num_child_elim:                    0
% 7.58/1.49  inst_num_of_dismatching_blockings:      585
% 7.58/1.49  inst_num_of_non_proper_insts:           1930
% 7.58/1.49  inst_num_of_duplicates:                 0
% 7.58/1.49  inst_inst_num_from_inst_to_res:         0
% 7.58/1.49  inst_dismatching_checking_time:         0.
% 7.58/1.49  
% 7.58/1.49  ------ Resolution
% 7.58/1.49  
% 7.58/1.49  res_num_of_clauses:                     0
% 7.58/1.49  res_num_in_passive:                     0
% 7.58/1.49  res_num_in_active:                      0
% 7.58/1.49  res_num_of_loops:                       251
% 7.58/1.49  res_forward_subset_subsumed:            57
% 7.58/1.49  res_backward_subset_subsumed:           4
% 7.58/1.49  res_forward_subsumed:                   0
% 7.58/1.49  res_backward_subsumed:                  0
% 7.58/1.49  res_forward_subsumption_resolution:     3
% 7.58/1.49  res_backward_subsumption_resolution:    0
% 7.58/1.49  res_clause_to_clause_subsumption:       1561
% 7.58/1.49  res_orphan_elimination:                 0
% 7.58/1.49  res_tautology_del:                      79
% 7.58/1.49  res_num_eq_res_simplified:              0
% 7.58/1.49  res_num_sel_changes:                    0
% 7.58/1.49  res_moves_from_active_to_pass:          0
% 7.58/1.49  
% 7.58/1.49  ------ Superposition
% 7.58/1.49  
% 7.58/1.49  sup_time_total:                         0.
% 7.58/1.49  sup_time_generating:                    0.
% 7.58/1.49  sup_time_sim_full:                      0.
% 7.58/1.49  sup_time_sim_immed:                     0.
% 7.58/1.49  
% 7.58/1.49  sup_num_of_clauses:                     339
% 7.58/1.49  sup_num_in_active:                      96
% 7.58/1.49  sup_num_in_passive:                     243
% 7.58/1.49  sup_num_of_loops:                       164
% 7.58/1.49  sup_fw_superposition:                   200
% 7.58/1.49  sup_bw_superposition:                   237
% 7.58/1.49  sup_immediate_simplified:               27
% 7.58/1.49  sup_given_eliminated:                   1
% 7.58/1.49  comparisons_done:                       0
% 7.58/1.49  comparisons_avoided:                    39
% 7.58/1.49  
% 7.58/1.49  ------ Simplifications
% 7.58/1.49  
% 7.58/1.49  
% 7.58/1.49  sim_fw_subset_subsumed:                 22
% 7.58/1.49  sim_bw_subset_subsumed:                 30
% 7.58/1.49  sim_fw_subsumed:                        3
% 7.58/1.49  sim_bw_subsumed:                        11
% 7.58/1.49  sim_fw_subsumption_res:                 0
% 7.58/1.49  sim_bw_subsumption_res:                 0
% 7.58/1.49  sim_tautology_del:                      14
% 7.58/1.49  sim_eq_tautology_del:                   13
% 7.58/1.49  sim_eq_res_simp:                        1
% 7.58/1.49  sim_fw_demodulated:                     1
% 7.58/1.49  sim_bw_demodulated:                     45
% 7.58/1.49  sim_light_normalised:                   3
% 7.58/1.49  sim_joinable_taut:                      0
% 7.58/1.49  sim_joinable_simp:                      0
% 7.58/1.49  sim_ac_normalised:                      0
% 7.58/1.49  sim_smt_subsumption:                    0
% 7.58/1.49  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:05 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  167 (2124 expanded)
%              Number of clauses        :  100 ( 708 expanded)
%              Number of leaves         :   22 ( 443 expanded)
%              Depth                    :   23
%              Number of atoms          :  558 (9811 expanded)
%              Number of equality atoms :  253 (2909 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK8,X4) != sK5
          | ~ m1_subset_1(X4,sK6) )
      & r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8))
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK8,sK6,sK7)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ! [X4] :
        ( k1_funct_1(sK8,X4) != sK5
        | ~ m1_subset_1(X4,sK6) )
    & r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK8,sK6,sK7)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f26,f43])).

fof(f76,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f74,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f44])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f78,plain,(
    ! [X4] :
      ( k1_funct_1(sK8,X4) != sK5
      | ~ m1_subset_1(X4,sK6) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_874,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_877,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1383,plain,
    ( k1_relset_1(sK6,sK7,sK8) = sK6
    | sK7 = k1_xboole_0
    | v1_funct_2(sK8,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_877])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1384,plain,
    ( ~ v1_funct_2(sK8,sK6,sK7)
    | k1_relset_1(sK6,sK7,sK8) = sK6
    | sK7 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1383])).

cnf(c_1817,plain,
    ( sK7 = k1_xboole_0
    | k1_relset_1(sK6,sK7,sK8) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1383,c_32,c_1384])).

cnf(c_1818,plain,
    ( k1_relset_1(sK6,sK7,sK8) = sK6
    | sK7 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1817])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_887,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1870,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_874,c_887])).

cnf(c_2313,plain,
    ( k1_relat_1(sK8) = sK6
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1818,c_1870])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_889,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4112,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | r2_hidden(sK4(sK8,X0),sK6) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_889])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1211,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1212,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_4549,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | r2_hidden(sK4(sK8,X0),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4112,c_34,c_36,c_1212])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_1])).

cnf(c_253,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_871,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_4559,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK4(sK8,X0),sK6) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4549,c_871])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_886,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1614,plain,
    ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_874,c_886])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_875,plain,
    ( r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1735,plain,
    ( r2_hidden(sK5,k2_relat_1(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1614,c_875])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_890,plain,
    ( k1_funct_1(X0,sK4(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3931,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK5)) = sK5
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_890])).

cnf(c_1741,plain,
    ( r2_hidden(sK5,k2_relat_1(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1735])).

cnf(c_2237,plain,
    ( ~ r2_hidden(sK5,k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,sK4(sK8,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4149,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3931,c_33,c_31,c_1211,c_1741,c_2237])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(X0,sK6)
    | k1_funct_1(sK8,X0) != sK5 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_876,plain,
    ( k1_funct_1(sK8,X0) != sK5
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4152,plain,
    ( m1_subset_1(sK4(sK8,sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4149,c_876])).

cnf(c_4575,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK5,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4559,c_4152])).

cnf(c_4693,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4575,c_1735])).

cnf(c_4704,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4693,c_874])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_881,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4904,plain,
    ( sK6 = k1_xboole_0
    | sK8 = k1_xboole_0
    | v1_funct_2(sK8,sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4704,c_881])).

cnf(c_35,plain,
    ( v1_funct_2(sK8,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_323,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_348,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1515,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_335,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1345,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK8,sK6,sK7)
    | X2 != sK7
    | X1 != sK6
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_1514,plain,
    ( v1_funct_2(sK8,X0,X1)
    | ~ v1_funct_2(sK8,sK6,sK7)
    | X1 != sK7
    | X0 != sK6
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_1717,plain,
    ( v1_funct_2(sK8,sK6,X0)
    | ~ v1_funct_2(sK8,sK6,sK7)
    | X0 != sK7
    | sK6 != sK6
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_1719,plain,
    ( X0 != sK7
    | sK6 != sK6
    | sK8 != sK8
    | v1_funct_2(sK8,sK6,X0) = iProver_top
    | v1_funct_2(sK8,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1717])).

cnf(c_1721,plain,
    ( sK6 != sK6
    | sK8 != sK8
    | k1_xboole_0 != sK7
    | v1_funct_2(sK8,sK6,sK7) != iProver_top
    | v1_funct_2(sK8,sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_1718,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_324,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2361,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_2362,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_885,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2299,plain,
    ( k7_relset_1(sK6,sK7,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_874,c_885])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_883,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2701,plain,
    ( k7_relset_1(sK6,sK7,sK8,sK6) = k2_relset_1(sK6,sK7,sK8) ),
    inference(superposition,[status(thm)],[c_874,c_883])).

cnf(c_2703,plain,
    ( k7_relset_1(sK6,sK7,sK8,sK6) = k2_relat_1(sK8) ),
    inference(light_normalisation,[status(thm)],[c_2701,c_1614])).

cnf(c_2817,plain,
    ( k9_relat_1(sK8,sK6) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_2299,c_2703])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_897,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_903,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3075,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_903])).

cnf(c_3405,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2817,c_3075])).

cnf(c_3432,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3405,c_36,c_1212])).

cnf(c_3442,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_3432])).

cnf(c_3447,plain,
    ( ~ v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3442])).

cnf(c_325,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5615,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_5617,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5615])).

cnf(c_5645,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4904,c_35,c_2,c_348,c_1515,c_1721,c_1718,c_1735,c_2362,c_3447,c_4575,c_5617])).

cnf(c_5656,plain,
    ( k9_relat_1(k1_xboole_0,sK6) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5645,c_2817])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_904,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_896,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3895,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_903])).

cnf(c_5951,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k9_relat_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_3895])).

cnf(c_6765,plain,
    ( v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5656,c_5951])).

cnf(c_888,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1473,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_888])).

cnf(c_5661,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5645,c_1473])).

cnf(c_1744,plain,
    ( v1_xboole_0(k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_903])).

cnf(c_5658,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5645,c_1744])).

cnf(c_117,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6765,c_5661,c_5658,c_117])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n010.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 17:37:44 EST 2020
% 0.10/0.33  % CPUTime    : 
% 0.10/0.33  % Running in FOF mode
% 3.61/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.98  
% 3.61/0.98  ------  iProver source info
% 3.61/0.98  
% 3.61/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.98  git: non_committed_changes: false
% 3.61/0.98  git: last_make_outside_of_git: false
% 3.61/0.98  
% 3.61/0.98  ------ 
% 3.61/0.98  ------ Parsing...
% 3.61/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.98  ------ Proving...
% 3.61/0.98  ------ Problem Properties 
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  clauses                                 34
% 3.61/0.98  conjectures                             5
% 3.61/0.98  EPR                                     8
% 3.61/0.98  Horn                                    26
% 3.61/0.98  unary                                   5
% 3.61/0.98  binary                                  10
% 3.61/0.98  lits                                    97
% 3.61/0.98  lits eq                                 21
% 3.61/0.98  fd_pure                                 0
% 3.61/0.98  fd_pseudo                               0
% 3.61/0.98  fd_cond                                 3
% 3.61/0.98  fd_pseudo_cond                          3
% 3.61/0.98  AC symbols                              0
% 3.61/0.98  
% 3.61/0.98  ------ Input Options Time Limit: Unbounded
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  ------ 
% 3.61/0.98  Current options:
% 3.61/0.98  ------ 
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  ------ Proving...
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  % SZS status Theorem for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  fof(f12,conjecture,(
% 3.61/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f13,negated_conjecture,(
% 3.61/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.61/0.98    inference(negated_conjecture,[],[f12])).
% 3.61/0.98  
% 3.61/0.98  fof(f25,plain,(
% 3.61/0.98    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 3.61/0.98    inference(ennf_transformation,[],[f13])).
% 3.61/0.98  
% 3.61/0.98  fof(f26,plain,(
% 3.61/0.98    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 3.61/0.98    inference(flattening,[],[f25])).
% 3.61/0.98  
% 3.61/0.98  fof(f43,plain,(
% 3.61/0.98    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK8,X4) != sK5 | ~m1_subset_1(X4,sK6)) & r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f44,plain,(
% 3.61/0.98    ! [X4] : (k1_funct_1(sK8,X4) != sK5 | ~m1_subset_1(X4,sK6)) & r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8)),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f26,f43])).
% 3.61/0.98  
% 3.61/0.98  fof(f76,plain,(
% 3.61/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 3.61/0.98    inference(cnf_transformation,[],[f44])).
% 3.61/0.98  
% 3.61/0.98  fof(f11,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f23,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(ennf_transformation,[],[f11])).
% 3.61/0.98  
% 3.61/0.98  fof(f24,plain,(
% 3.61/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(flattening,[],[f23])).
% 3.61/0.98  
% 3.61/0.98  fof(f42,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(nnf_transformation,[],[f24])).
% 3.61/0.98  
% 3.61/0.98  fof(f68,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f42])).
% 3.61/0.98  
% 3.61/0.98  fof(f75,plain,(
% 3.61/0.98    v1_funct_2(sK8,sK6,sK7)),
% 3.61/0.98    inference(cnf_transformation,[],[f44])).
% 3.61/0.98  
% 3.61/0.98  fof(f7,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f19,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(ennf_transformation,[],[f7])).
% 3.61/0.98  
% 3.61/0.98  fof(f63,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f19])).
% 3.61/0.98  
% 3.61/0.98  fof(f5,axiom,(
% 3.61/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f16,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.61/0.98    inference(ennf_transformation,[],[f5])).
% 3.61/0.98  
% 3.61/0.98  fof(f17,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.98    inference(flattening,[],[f16])).
% 3.61/0.98  
% 3.61/0.98  fof(f36,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.98    inference(nnf_transformation,[],[f17])).
% 3.61/0.98  
% 3.61/0.98  fof(f37,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.98    inference(rectify,[],[f36])).
% 3.61/0.98  
% 3.61/0.98  fof(f40,plain,(
% 3.61/0.98    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f39,plain,(
% 3.61/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f38,plain,(
% 3.61/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f41,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).
% 3.61/0.98  
% 3.61/0.98  fof(f56,plain,(
% 3.61/0.98    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f41])).
% 3.61/0.98  
% 3.61/0.98  fof(f82,plain,(
% 3.61/0.98    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.98    inference(equality_resolution,[],[f56])).
% 3.61/0.98  
% 3.61/0.98  fof(f74,plain,(
% 3.61/0.98    v1_funct_1(sK8)),
% 3.61/0.98    inference(cnf_transformation,[],[f44])).
% 3.61/0.98  
% 3.61/0.98  fof(f6,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f18,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(ennf_transformation,[],[f6])).
% 3.61/0.98  
% 3.61/0.98  fof(f62,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f18])).
% 3.61/0.98  
% 3.61/0.98  fof(f3,axiom,(
% 3.61/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f14,plain,(
% 3.61/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.61/0.98    inference(ennf_transformation,[],[f3])).
% 3.61/0.98  
% 3.61/0.98  fof(f31,plain,(
% 3.61/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.61/0.98    inference(nnf_transformation,[],[f14])).
% 3.61/0.98  
% 3.61/0.98  fof(f49,plain,(
% 3.61/0.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f31])).
% 3.61/0.98  
% 3.61/0.98  fof(f1,axiom,(
% 3.61/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f27,plain,(
% 3.61/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.61/0.98    inference(nnf_transformation,[],[f1])).
% 3.61/0.98  
% 3.61/0.98  fof(f28,plain,(
% 3.61/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.61/0.98    inference(rectify,[],[f27])).
% 3.61/0.98  
% 3.61/0.98  fof(f29,plain,(
% 3.61/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f30,plain,(
% 3.61/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.61/0.98  
% 3.61/0.98  fof(f45,plain,(
% 3.61/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f30])).
% 3.61/0.98  
% 3.61/0.98  fof(f8,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f20,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(ennf_transformation,[],[f8])).
% 3.61/0.98  
% 3.61/0.98  fof(f64,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f20])).
% 3.61/0.98  
% 3.61/0.98  fof(f77,plain,(
% 3.61/0.98    r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8))),
% 3.61/0.98    inference(cnf_transformation,[],[f44])).
% 3.61/0.98  
% 3.61/0.98  fof(f57,plain,(
% 3.61/0.98    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f41])).
% 3.61/0.98  
% 3.61/0.98  fof(f81,plain,(
% 3.61/0.98    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.98    inference(equality_resolution,[],[f57])).
% 3.61/0.98  
% 3.61/0.98  fof(f78,plain,(
% 3.61/0.98    ( ! [X4] : (k1_funct_1(sK8,X4) != sK5 | ~m1_subset_1(X4,sK6)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f44])).
% 3.61/0.98  
% 3.61/0.98  fof(f72,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f42])).
% 3.61/0.98  
% 3.61/0.98  fof(f85,plain,(
% 3.61/0.98    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.61/0.98    inference(equality_resolution,[],[f72])).
% 3.61/0.98  
% 3.61/0.98  fof(f2,axiom,(
% 3.61/0.98    v1_xboole_0(k1_xboole_0)),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f47,plain,(
% 3.61/0.98    v1_xboole_0(k1_xboole_0)),
% 3.61/0.98    inference(cnf_transformation,[],[f2])).
% 3.61/0.98  
% 3.61/0.98  fof(f9,axiom,(
% 3.61/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f21,plain,(
% 3.61/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(ennf_transformation,[],[f9])).
% 3.61/0.98  
% 3.61/0.98  fof(f65,plain,(
% 3.61/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f21])).
% 3.61/0.98  
% 3.61/0.98  fof(f10,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f22,plain,(
% 3.61/0.98    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(ennf_transformation,[],[f10])).
% 3.61/0.98  
% 3.61/0.98  fof(f66,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f22])).
% 3.61/0.98  
% 3.61/0.98  fof(f4,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.61/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f15,plain,(
% 3.61/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(ennf_transformation,[],[f4])).
% 3.61/0.98  
% 3.61/0.98  fof(f32,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(nnf_transformation,[],[f15])).
% 3.61/0.98  
% 3.61/0.98  fof(f33,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(rectify,[],[f32])).
% 3.61/0.98  
% 3.61/0.98  fof(f34,plain,(
% 3.61/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f35,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.61/0.98  
% 3.61/0.98  fof(f54,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f35])).
% 3.61/0.98  
% 3.61/0.98  fof(f46,plain,(
% 3.61/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f30])).
% 3.61/0.98  
% 3.61/0.98  fof(f53,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f35])).
% 3.61/0.98  
% 3.61/0.98  cnf(c_31,negated_conjecture,
% 3.61/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 3.61/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_874,plain,
% 3.61/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_28,plain,
% 3.61/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.61/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.61/0.98      | k1_xboole_0 = X2 ),
% 3.61/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_877,plain,
% 3.61/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.61/0.98      | k1_xboole_0 = X1
% 3.61/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1383,plain,
% 3.61/0.98      ( k1_relset_1(sK6,sK7,sK8) = sK6
% 3.61/0.98      | sK7 = k1_xboole_0
% 3.61/0.98      | v1_funct_2(sK8,sK6,sK7) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_874,c_877]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_32,negated_conjecture,
% 3.61/0.98      ( v1_funct_2(sK8,sK6,sK7) ),
% 3.61/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1384,plain,
% 3.61/0.98      ( ~ v1_funct_2(sK8,sK6,sK7)
% 3.61/0.98      | k1_relset_1(sK6,sK7,sK8) = sK6
% 3.61/0.98      | sK7 = k1_xboole_0 ),
% 3.61/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1383]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1817,plain,
% 3.61/0.98      ( sK7 = k1_xboole_0 | k1_relset_1(sK6,sK7,sK8) = sK6 ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_1383,c_32,c_1384]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1818,plain,
% 3.61/0.98      ( k1_relset_1(sK6,sK7,sK8) = sK6 | sK7 = k1_xboole_0 ),
% 3.61/0.98      inference(renaming,[status(thm)],[c_1817]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_18,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_887,plain,
% 3.61/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1870,plain,
% 3.61/0.98      ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_874,c_887]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2313,plain,
% 3.61/0.98      ( k1_relat_1(sK8) = sK6 | sK7 = k1_xboole_0 ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1818,c_1870]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_16,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.61/0.98      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 3.61/0.98      | ~ v1_funct_1(X1)
% 3.61/0.98      | ~ v1_relat_1(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_889,plain,
% 3.61/0.98      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.61/0.98      | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.61/0.98      | v1_funct_1(X1) != iProver_top
% 3.61/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4112,plain,
% 3.61/0.98      ( sK7 = k1_xboole_0
% 3.61/0.98      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.61/0.98      | r2_hidden(sK4(sK8,X0),sK6) = iProver_top
% 3.61/0.98      | v1_funct_1(sK8) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_2313,c_889]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_33,negated_conjecture,
% 3.61/0.98      ( v1_funct_1(sK8) ),
% 3.61/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_34,plain,
% 3.61/0.98      ( v1_funct_1(sK8) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_36,plain,
% 3.61/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_17,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | v1_relat_1(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1211,plain,
% 3.61/0.98      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.61/0.98      | v1_relat_1(sK8) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1212,plain,
% 3.61/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_1211]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4549,plain,
% 3.61/0.98      ( sK7 = k1_xboole_0
% 3.61/0.98      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.61/0.98      | r2_hidden(sK4(sK8,X0),sK6) = iProver_top ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_4112,c_34,c_36,c_1212]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5,plain,
% 3.61/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_252,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.61/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5,c_1]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_253,plain,
% 3.61/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.61/0.98      inference(renaming,[status(thm)],[c_252]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_871,plain,
% 3.61/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.61/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4559,plain,
% 3.61/0.98      ( sK7 = k1_xboole_0
% 3.61/0.98      | m1_subset_1(sK4(sK8,X0),sK6) = iProver_top
% 3.61/0.98      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_4549,c_871]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_19,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_886,plain,
% 3.61/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1614,plain,
% 3.61/0.98      ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_874,c_886]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_30,negated_conjecture,
% 3.61/0.98      ( r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8)) ),
% 3.61/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_875,plain,
% 3.61/0.98      ( r2_hidden(sK5,k2_relset_1(sK6,sK7,sK8)) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1735,plain,
% 3.61/0.98      ( r2_hidden(sK5,k2_relat_1(sK8)) = iProver_top ),
% 3.61/0.98      inference(demodulation,[status(thm)],[c_1614,c_875]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_15,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.61/0.98      | ~ v1_funct_1(X1)
% 3.61/0.98      | ~ v1_relat_1(X1)
% 3.61/0.98      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 3.61/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_890,plain,
% 3.61/0.98      ( k1_funct_1(X0,sK4(X0,X1)) = X1
% 3.61/0.98      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.61/0.98      | v1_funct_1(X0) != iProver_top
% 3.61/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3931,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK4(sK8,sK5)) = sK5
% 3.61/0.98      | v1_funct_1(sK8) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1735,c_890]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1741,plain,
% 3.61/0.98      ( r2_hidden(sK5,k2_relat_1(sK8)) ),
% 3.61/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1735]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2237,plain,
% 3.61/0.98      ( ~ r2_hidden(sK5,k2_relat_1(sK8))
% 3.61/0.98      | ~ v1_funct_1(sK8)
% 3.61/0.98      | ~ v1_relat_1(sK8)
% 3.61/0.98      | k1_funct_1(sK8,sK4(sK8,sK5)) = sK5 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4149,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK4(sK8,sK5)) = sK5 ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_3931,c_33,c_31,c_1211,c_1741,c_2237]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_29,negated_conjecture,
% 3.61/0.98      ( ~ m1_subset_1(X0,sK6) | k1_funct_1(sK8,X0) != sK5 ),
% 3.61/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_876,plain,
% 3.61/0.98      ( k1_funct_1(sK8,X0) != sK5 | m1_subset_1(X0,sK6) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4152,plain,
% 3.61/0.98      ( m1_subset_1(sK4(sK8,sK5),sK6) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_4149,c_876]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4575,plain,
% 3.61/0.98      ( sK7 = k1_xboole_0
% 3.61/0.98      | r2_hidden(sK5,k2_relat_1(sK8)) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_4559,c_4152]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4693,plain,
% 3.61/0.98      ( sK7 = k1_xboole_0 ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_4575,c_1735]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4704,plain,
% 3.61/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0))) = iProver_top ),
% 3.61/0.98      inference(demodulation,[status(thm)],[c_4693,c_874]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_24,plain,
% 3.61/0.98      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.61/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.61/0.98      | k1_xboole_0 = X1
% 3.61/0.98      | k1_xboole_0 = X0 ),
% 3.61/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_881,plain,
% 3.61/0.98      ( k1_xboole_0 = X0
% 3.61/0.98      | k1_xboole_0 = X1
% 3.61/0.98      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.61/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4904,plain,
% 3.61/0.98      ( sK6 = k1_xboole_0
% 3.61/0.98      | sK8 = k1_xboole_0
% 3.61/0.98      | v1_funct_2(sK8,sK6,k1_xboole_0) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_4704,c_881]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_35,plain,
% 3.61/0.98      ( v1_funct_2(sK8,sK6,sK7) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2,plain,
% 3.61/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_323,plain,( X0 = X0 ),theory(equality) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_348,plain,
% 3.61/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_323]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1515,plain,
% 3.61/0.98      ( sK8 = sK8 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_323]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_335,plain,
% 3.61/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.61/0.98      | v1_funct_2(X3,X4,X5)
% 3.61/0.98      | X3 != X0
% 3.61/0.98      | X4 != X1
% 3.61/0.98      | X5 != X2 ),
% 3.61/0.98      theory(equality) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1345,plain,
% 3.61/0.98      ( v1_funct_2(X0,X1,X2)
% 3.61/0.98      | ~ v1_funct_2(sK8,sK6,sK7)
% 3.61/0.98      | X2 != sK7
% 3.61/0.98      | X1 != sK6
% 3.61/0.98      | X0 != sK8 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_335]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1514,plain,
% 3.61/0.98      ( v1_funct_2(sK8,X0,X1)
% 3.61/0.98      | ~ v1_funct_2(sK8,sK6,sK7)
% 3.61/0.98      | X1 != sK7
% 3.61/0.98      | X0 != sK6
% 3.61/0.98      | sK8 != sK8 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1345]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1717,plain,
% 3.61/0.98      ( v1_funct_2(sK8,sK6,X0)
% 3.61/0.98      | ~ v1_funct_2(sK8,sK6,sK7)
% 3.61/0.98      | X0 != sK7
% 3.61/0.98      | sK6 != sK6
% 3.61/0.98      | sK8 != sK8 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1514]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1719,plain,
% 3.61/0.98      ( X0 != sK7
% 3.61/0.98      | sK6 != sK6
% 3.61/0.98      | sK8 != sK8
% 3.61/0.98      | v1_funct_2(sK8,sK6,X0) = iProver_top
% 3.61/0.98      | v1_funct_2(sK8,sK6,sK7) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_1717]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1721,plain,
% 3.61/0.98      ( sK6 != sK6
% 3.61/0.98      | sK8 != sK8
% 3.61/0.98      | k1_xboole_0 != sK7
% 3.61/0.98      | v1_funct_2(sK8,sK6,sK7) != iProver_top
% 3.61/0.98      | v1_funct_2(sK8,sK6,k1_xboole_0) = iProver_top ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1719]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1718,plain,
% 3.61/0.98      ( sK6 = sK6 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_323]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_324,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2361,plain,
% 3.61/0.98      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_324]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2362,plain,
% 3.61/0.98      ( sK7 != k1_xboole_0
% 3.61/0.98      | k1_xboole_0 = sK7
% 3.61/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_2361]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_20,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.61/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_885,plain,
% 3.61/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2299,plain,
% 3.61/0.98      ( k7_relset_1(sK6,sK7,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_874,c_885]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_22,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_883,plain,
% 3.61/0.98      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2701,plain,
% 3.61/0.98      ( k7_relset_1(sK6,sK7,sK8,sK6) = k2_relset_1(sK6,sK7,sK8) ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_874,c_883]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2703,plain,
% 3.61/0.98      ( k7_relset_1(sK6,sK7,sK8,sK6) = k2_relat_1(sK8) ),
% 3.61/0.98      inference(light_normalisation,[status(thm)],[c_2701,c_1614]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2817,plain,
% 3.61/0.98      ( k9_relat_1(sK8,sK6) = k2_relat_1(sK8) ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_2299,c_2703]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_8,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.61/0.98      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.61/0.98      | ~ v1_relat_1(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_897,plain,
% 3.61/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.61/0.98      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 3.61/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_903,plain,
% 3.61/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.61/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3075,plain,
% 3.61/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.61/0.98      | v1_relat_1(X1) != iProver_top
% 3.61/0.98      | v1_xboole_0(X2) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_897,c_903]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3405,plain,
% 3.61/0.98      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top
% 3.61/0.98      | v1_xboole_0(sK6) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_2817,c_3075]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3432,plain,
% 3.61/0.98      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.61/0.98      | v1_xboole_0(sK6) != iProver_top ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_3405,c_36,c_1212]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3442,plain,
% 3.61/0.98      ( v1_xboole_0(sK6) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1735,c_3432]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3447,plain,
% 3.61/0.98      ( ~ v1_xboole_0(sK6) ),
% 3.61/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3442]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_325,plain,
% 3.61/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.61/0.98      theory(equality) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5615,plain,
% 3.61/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_325]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5617,plain,
% 3.61/0.98      ( v1_xboole_0(sK6)
% 3.61/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 3.61/0.98      | sK6 != k1_xboole_0 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_5615]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5645,plain,
% 3.61/0.98      ( sK8 = k1_xboole_0 ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_4904,c_35,c_2,c_348,c_1515,c_1721,c_1718,c_1735,
% 3.61/0.98                 c_2362,c_3447,c_4575,c_5617]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5656,plain,
% 3.61/0.98      ( k9_relat_1(k1_xboole_0,sK6) = k2_relat_1(k1_xboole_0) ),
% 3.61/0.98      inference(demodulation,[status(thm)],[c_5645,c_2817]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_0,plain,
% 3.61/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_904,plain,
% 3.61/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.61/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_9,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.61/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.61/0.98      | ~ v1_relat_1(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_896,plain,
% 3.61/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.61/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.61/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3895,plain,
% 3.61/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.61/0.98      | v1_relat_1(X1) != iProver_top
% 3.61/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_896,c_903]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5951,plain,
% 3.61/0.98      ( v1_relat_1(X0) != iProver_top
% 3.61/0.98      | v1_xboole_0(X0) != iProver_top
% 3.61/0.98      | v1_xboole_0(k9_relat_1(X0,X1)) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_904,c_3895]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_6765,plain,
% 3.61/0.98      ( v1_relat_1(k1_xboole_0) != iProver_top
% 3.61/0.98      | v1_xboole_0(k2_relat_1(k1_xboole_0)) = iProver_top
% 3.61/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_5656,c_5951]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_888,plain,
% 3.61/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1473,plain,
% 3.61/0.98      ( v1_relat_1(sK8) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_874,c_888]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5661,plain,
% 3.61/0.98      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.61/0.98      inference(demodulation,[status(thm)],[c_5645,c_1473]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1744,plain,
% 3.61/0.98      ( v1_xboole_0(k2_relat_1(sK8)) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1735,c_903]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5658,plain,
% 3.61/0.98      ( v1_xboole_0(k2_relat_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.98      inference(demodulation,[status(thm)],[c_5645,c_1744]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_117,plain,
% 3.61/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(contradiction,plain,
% 3.61/0.98      ( $false ),
% 3.61/0.98      inference(minisat,[status(thm)],[c_6765,c_5661,c_5658,c_117]) ).
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  ------                               Statistics
% 3.61/0.98  
% 3.61/0.98  ------ Selected
% 3.61/0.98  
% 3.61/0.98  total_time:                             0.277
% 3.61/0.98  
%------------------------------------------------------------------------------

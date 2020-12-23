%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:52 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 448 expanded)
%              Number of clauses        :   81 ( 147 expanded)
%              Number of leaves         :   18 ( 113 expanded)
%              Depth                    :   22
%              Number of atoms          :  534 (2534 expanded)
%              Number of equality atoms :  210 ( 639 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f15])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ r2_hidden(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ r2_hidden(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f24,f39,f38])).

fof(f68,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f21])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

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

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f72,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(nnf_transformation,[],[f14])).

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

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_663,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_664,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),X1)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_1736,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_665,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_1393,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1952,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_440,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_441,plain,
    ( v1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_1955,plain,
    ( v1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_1956,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_2310,plain,
    ( r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1736,c_665,c_1952,c_1956])).

cnf(c_2311,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2310])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_387,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | k1_relset_1(X0,X1,sK7) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_978,plain,
    ( k1_relset_1(X0,X1,sK7) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK5 != X1
    | sK4 != X0
    | sK7 != sK7
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_387])).

cnf(c_979,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_978])).

cnf(c_1052,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_979])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_431,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_432,plain,
    ( k1_relset_1(X0,X1,sK7) = k1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_1951,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(equality_resolution,[status(thm)],[c_432])).

cnf(c_2040,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1052,c_1951])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_648,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_649,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_1737,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_650,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_2384,plain,
    ( r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1737,c_650,c_1952,c_1956])).

cnf(c_2385,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2384])).

cnf(c_2392,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2040,c_2385])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_422,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_423,plain,
    ( k7_relset_1(X0,X1,sK7,X2) = k9_relat_1(sK7,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_1963,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(equality_resolution,[status(thm)],[c_423])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1746,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1990,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1963,c_1746])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_678,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_679,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_1735,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_680,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_2288,plain,
    ( r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1735,c_680,c_1952,c_1956])).

cnf(c_2289,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2288])).

cnf(c_2297,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
    inference(superposition,[status(thm)],[c_1990,c_2289])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1747,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3225,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2297,c_1747])).

cnf(c_7890,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2392,c_3225])).

cnf(c_9390,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7890,c_1990])).

cnf(c_9391,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_9390])).

cnf(c_9396,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_9391])).

cnf(c_9399,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9396,c_1990])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1749,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_371,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_29])).

cnf(c_372,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK7)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1744,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_2259,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1744])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1753,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3364,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2259,c_1753])).

cnf(c_3722,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_3364])).

cnf(c_5409,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3722,c_1952,c_1956])).

cnf(c_5410,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_5409])).

cnf(c_5423,plain,
    ( r2_hidden(sK8,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1990,c_5410])).

cnf(c_9404,plain,
    ( r2_hidden(sK8,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9399,c_5423])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_360,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_361,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_2103,plain,
    ( ~ r2_hidden(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_2106,plain,
    ( r2_hidden(sK8,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2103])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9404,c_2106])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.53/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
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
% 3.53/1.00  
% 3.53/1.00  ------ Input Options
% 3.53/1.00  
% 3.53/1.00  --out_options                           all
% 3.53/1.00  --tptp_safe_out                         true
% 3.53/1.00  --problem_path                          ""
% 3.53/1.00  --include_path                          ""
% 3.53/1.00  --clausifier                            res/vclausify_rel
% 3.53/1.00  --clausifier_options                    --mode clausify
% 3.53/1.00  --stdin                                 false
% 3.53/1.00  --stats_out                             all
% 3.53/1.00  
% 3.53/1.00  ------ General Options
% 3.53/1.00  
% 3.53/1.00  --fof                                   false
% 3.53/1.00  --time_out_real                         305.
% 3.53/1.00  --time_out_virtual                      -1.
% 3.53/1.00  --symbol_type_check                     false
% 3.53/1.00  --clausify_out                          false
% 3.53/1.00  --sig_cnt_out                           false
% 3.53/1.00  --trig_cnt_out                          false
% 3.53/1.00  --trig_cnt_out_tolerance                1.
% 3.53/1.00  --trig_cnt_out_sk_spl                   false
% 3.53/1.00  --abstr_cl_out                          false
% 3.53/1.00  
% 3.53/1.00  ------ Global Options
% 3.53/1.00  
% 3.53/1.00  --schedule                              default
% 3.53/1.00  --add_important_lit                     false
% 3.53/1.00  --prop_solver_per_cl                    1000
% 3.53/1.00  --min_unsat_core                        false
% 3.53/1.00  --soft_assumptions                      false
% 3.53/1.00  --soft_lemma_size                       3
% 3.53/1.00  --prop_impl_unit_size                   0
% 3.53/1.00  --prop_impl_unit                        []
% 3.53/1.00  --share_sel_clauses                     true
% 3.53/1.00  --reset_solvers                         false
% 3.53/1.00  --bc_imp_inh                            [conj_cone]
% 3.53/1.00  --conj_cone_tolerance                   3.
% 3.53/1.00  --extra_neg_conj                        none
% 3.53/1.00  --large_theory_mode                     true
% 3.53/1.00  --prolific_symb_bound                   200
% 3.53/1.00  --lt_threshold                          2000
% 3.53/1.00  --clause_weak_htbl                      true
% 3.53/1.00  --gc_record_bc_elim                     false
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing Options
% 3.53/1.00  
% 3.53/1.00  --preprocessing_flag                    true
% 3.53/1.00  --time_out_prep_mult                    0.1
% 3.53/1.00  --splitting_mode                        input
% 3.53/1.00  --splitting_grd                         true
% 3.53/1.00  --splitting_cvd                         false
% 3.53/1.00  --splitting_cvd_svl                     false
% 3.53/1.00  --splitting_nvd                         32
% 3.53/1.00  --sub_typing                            true
% 3.53/1.00  --prep_gs_sim                           true
% 3.53/1.00  --prep_unflatten                        true
% 3.53/1.00  --prep_res_sim                          true
% 3.53/1.00  --prep_upred                            true
% 3.53/1.00  --prep_sem_filter                       exhaustive
% 3.53/1.00  --prep_sem_filter_out                   false
% 3.53/1.00  --pred_elim                             true
% 3.53/1.00  --res_sim_input                         true
% 3.53/1.00  --eq_ax_congr_red                       true
% 3.53/1.00  --pure_diseq_elim                       true
% 3.53/1.00  --brand_transform                       false
% 3.53/1.00  --non_eq_to_eq                          false
% 3.53/1.00  --prep_def_merge                        true
% 3.53/1.00  --prep_def_merge_prop_impl              false
% 3.53/1.00  --prep_def_merge_mbd                    true
% 3.53/1.00  --prep_def_merge_tr_red                 false
% 3.53/1.00  --prep_def_merge_tr_cl                  false
% 3.53/1.00  --smt_preprocessing                     true
% 3.53/1.00  --smt_ac_axioms                         fast
% 3.53/1.00  --preprocessed_out                      false
% 3.53/1.00  --preprocessed_stats                    false
% 3.53/1.00  
% 3.53/1.00  ------ Abstraction refinement Options
% 3.53/1.00  
% 3.53/1.00  --abstr_ref                             []
% 3.53/1.00  --abstr_ref_prep                        false
% 3.53/1.00  --abstr_ref_until_sat                   false
% 3.53/1.00  --abstr_ref_sig_restrict                funpre
% 3.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.00  --abstr_ref_under                       []
% 3.53/1.00  
% 3.53/1.00  ------ SAT Options
% 3.53/1.00  
% 3.53/1.00  --sat_mode                              false
% 3.53/1.00  --sat_fm_restart_options                ""
% 3.53/1.00  --sat_gr_def                            false
% 3.53/1.00  --sat_epr_types                         true
% 3.53/1.00  --sat_non_cyclic_types                  false
% 3.53/1.00  --sat_finite_models                     false
% 3.53/1.00  --sat_fm_lemmas                         false
% 3.53/1.00  --sat_fm_prep                           false
% 3.53/1.00  --sat_fm_uc_incr                        true
% 3.53/1.00  --sat_out_model                         small
% 3.53/1.00  --sat_out_clauses                       false
% 3.53/1.00  
% 3.53/1.00  ------ QBF Options
% 3.53/1.00  
% 3.53/1.00  --qbf_mode                              false
% 3.53/1.00  --qbf_elim_univ                         false
% 3.53/1.00  --qbf_dom_inst                          none
% 3.53/1.00  --qbf_dom_pre_inst                      false
% 3.53/1.00  --qbf_sk_in                             false
% 3.53/1.00  --qbf_pred_elim                         true
% 3.53/1.00  --qbf_split                             512
% 3.53/1.00  
% 3.53/1.00  ------ BMC1 Options
% 3.53/1.00  
% 3.53/1.00  --bmc1_incremental                      false
% 3.53/1.00  --bmc1_axioms                           reachable_all
% 3.53/1.00  --bmc1_min_bound                        0
% 3.53/1.00  --bmc1_max_bound                        -1
% 3.53/1.00  --bmc1_max_bound_default                -1
% 3.53/1.00  --bmc1_symbol_reachability              true
% 3.53/1.00  --bmc1_property_lemmas                  false
% 3.53/1.00  --bmc1_k_induction                      false
% 3.53/1.00  --bmc1_non_equiv_states                 false
% 3.53/1.00  --bmc1_deadlock                         false
% 3.53/1.00  --bmc1_ucm                              false
% 3.53/1.00  --bmc1_add_unsat_core                   none
% 3.53/1.00  --bmc1_unsat_core_children              false
% 3.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.00  --bmc1_out_stat                         full
% 3.53/1.00  --bmc1_ground_init                      false
% 3.53/1.00  --bmc1_pre_inst_next_state              false
% 3.53/1.00  --bmc1_pre_inst_state                   false
% 3.53/1.00  --bmc1_pre_inst_reach_state             false
% 3.53/1.00  --bmc1_out_unsat_core                   false
% 3.53/1.00  --bmc1_aig_witness_out                  false
% 3.53/1.00  --bmc1_verbose                          false
% 3.53/1.00  --bmc1_dump_clauses_tptp                false
% 3.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.00  --bmc1_dump_file                        -
% 3.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.00  --bmc1_ucm_extend_mode                  1
% 3.53/1.00  --bmc1_ucm_init_mode                    2
% 3.53/1.00  --bmc1_ucm_cone_mode                    none
% 3.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.00  --bmc1_ucm_relax_model                  4
% 3.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.00  --bmc1_ucm_layered_model                none
% 3.53/1.00  --bmc1_ucm_max_lemma_size               10
% 3.53/1.00  
% 3.53/1.00  ------ AIG Options
% 3.53/1.00  
% 3.53/1.00  --aig_mode                              false
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation Options
% 3.53/1.00  
% 3.53/1.00  --instantiation_flag                    true
% 3.53/1.00  --inst_sos_flag                         false
% 3.53/1.00  --inst_sos_phase                        true
% 3.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel_side                     num_symb
% 3.53/1.00  --inst_solver_per_active                1400
% 3.53/1.00  --inst_solver_calls_frac                1.
% 3.53/1.00  --inst_passive_queue_type               priority_queues
% 3.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.00  --inst_passive_queues_freq              [25;2]
% 3.53/1.00  --inst_dismatching                      true
% 3.53/1.00  --inst_eager_unprocessed_to_passive     true
% 3.53/1.00  --inst_prop_sim_given                   true
% 3.53/1.00  --inst_prop_sim_new                     false
% 3.53/1.00  --inst_subs_new                         false
% 3.53/1.00  --inst_eq_res_simp                      false
% 3.53/1.00  --inst_subs_given                       false
% 3.53/1.00  --inst_orphan_elimination               true
% 3.53/1.00  --inst_learning_loop_flag               true
% 3.53/1.00  --inst_learning_start                   3000
% 3.53/1.00  --inst_learning_factor                  2
% 3.53/1.00  --inst_start_prop_sim_after_learn       3
% 3.53/1.00  --inst_sel_renew                        solver
% 3.53/1.00  --inst_lit_activity_flag                true
% 3.53/1.00  --inst_restr_to_given                   false
% 3.53/1.00  --inst_activity_threshold               500
% 3.53/1.00  --inst_out_proof                        true
% 3.53/1.00  
% 3.53/1.00  ------ Resolution Options
% 3.53/1.00  
% 3.53/1.00  --resolution_flag                       true
% 3.53/1.00  --res_lit_sel                           adaptive
% 3.53/1.00  --res_lit_sel_side                      none
% 3.53/1.00  --res_ordering                          kbo
% 3.53/1.00  --res_to_prop_solver                    active
% 3.53/1.00  --res_prop_simpl_new                    false
% 3.53/1.00  --res_prop_simpl_given                  true
% 3.53/1.00  --res_passive_queue_type                priority_queues
% 3.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.00  --res_passive_queues_freq               [15;5]
% 3.53/1.00  --res_forward_subs                      full
% 3.53/1.00  --res_backward_subs                     full
% 3.53/1.00  --res_forward_subs_resolution           true
% 3.53/1.00  --res_backward_subs_resolution          true
% 3.53/1.00  --res_orphan_elimination                true
% 3.53/1.00  --res_time_limit                        2.
% 3.53/1.00  --res_out_proof                         true
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Options
% 3.53/1.00  
% 3.53/1.00  --superposition_flag                    true
% 3.53/1.00  --sup_passive_queue_type                priority_queues
% 3.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.00  --demod_completeness_check              fast
% 3.53/1.00  --demod_use_ground                      true
% 3.53/1.00  --sup_to_prop_solver                    passive
% 3.53/1.00  --sup_prop_simpl_new                    true
% 3.53/1.00  --sup_prop_simpl_given                  true
% 3.53/1.00  --sup_fun_splitting                     false
% 3.53/1.00  --sup_smt_interval                      50000
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Simplification Setup
% 3.53/1.00  
% 3.53/1.00  --sup_indices_passive                   []
% 3.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_full_bw                           [BwDemod]
% 3.53/1.00  --sup_immed_triv                        [TrivRules]
% 3.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_immed_bw_main                     []
% 3.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  
% 3.53/1.00  ------ Combination Options
% 3.53/1.00  
% 3.53/1.00  --comb_res_mult                         3
% 3.53/1.00  --comb_sup_mult                         2
% 3.53/1.00  --comb_inst_mult                        10
% 3.53/1.00  
% 3.53/1.00  ------ Debug Options
% 3.53/1.00  
% 3.53/1.00  --dbg_backtrace                         false
% 3.53/1.00  --dbg_dump_prop_clauses                 false
% 3.53/1.00  --dbg_dump_prop_clauses_file            -
% 3.53/1.00  --dbg_out_stat                          false
% 3.53/1.00  ------ Parsing...
% 3.53/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/1.00  ------ Proving...
% 3.53/1.00  ------ Problem Properties 
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  clauses                                 25
% 3.53/1.00  conjectures                             2
% 3.53/1.00  EPR                                     1
% 3.53/1.00  Horn                                    20
% 3.53/1.00  unary                                   2
% 3.53/1.00  binary                                  6
% 3.53/1.00  lits                                    75
% 3.53/1.00  lits eq                                 23
% 3.53/1.00  fd_pure                                 0
% 3.53/1.00  fd_pseudo                               0
% 3.53/1.00  fd_cond                                 0
% 3.53/1.00  fd_pseudo_cond                          4
% 3.53/1.00  AC symbols                              0
% 3.53/1.00  
% 3.53/1.00  ------ Schedule dynamic 5 is on 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  Current options:
% 3.53/1.00  ------ 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options
% 3.53/1.00  
% 3.53/1.00  --out_options                           all
% 3.53/1.00  --tptp_safe_out                         true
% 3.53/1.00  --problem_path                          ""
% 3.53/1.00  --include_path                          ""
% 3.53/1.00  --clausifier                            res/vclausify_rel
% 3.53/1.00  --clausifier_options                    --mode clausify
% 3.53/1.00  --stdin                                 false
% 3.53/1.00  --stats_out                             all
% 3.53/1.00  
% 3.53/1.00  ------ General Options
% 3.53/1.00  
% 3.53/1.00  --fof                                   false
% 3.53/1.00  --time_out_real                         305.
% 3.53/1.00  --time_out_virtual                      -1.
% 3.53/1.00  --symbol_type_check                     false
% 3.53/1.00  --clausify_out                          false
% 3.53/1.00  --sig_cnt_out                           false
% 3.53/1.00  --trig_cnt_out                          false
% 3.53/1.00  --trig_cnt_out_tolerance                1.
% 3.53/1.00  --trig_cnt_out_sk_spl                   false
% 3.53/1.00  --abstr_cl_out                          false
% 3.53/1.00  
% 3.53/1.00  ------ Global Options
% 3.53/1.00  
% 3.53/1.00  --schedule                              default
% 3.53/1.00  --add_important_lit                     false
% 3.53/1.00  --prop_solver_per_cl                    1000
% 3.53/1.00  --min_unsat_core                        false
% 3.53/1.00  --soft_assumptions                      false
% 3.53/1.00  --soft_lemma_size                       3
% 3.53/1.00  --prop_impl_unit_size                   0
% 3.53/1.00  --prop_impl_unit                        []
% 3.53/1.00  --share_sel_clauses                     true
% 3.53/1.00  --reset_solvers                         false
% 3.53/1.00  --bc_imp_inh                            [conj_cone]
% 3.53/1.00  --conj_cone_tolerance                   3.
% 3.53/1.00  --extra_neg_conj                        none
% 3.53/1.00  --large_theory_mode                     true
% 3.53/1.00  --prolific_symb_bound                   200
% 3.53/1.00  --lt_threshold                          2000
% 3.53/1.00  --clause_weak_htbl                      true
% 3.53/1.00  --gc_record_bc_elim                     false
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing Options
% 3.53/1.00  
% 3.53/1.00  --preprocessing_flag                    true
% 3.53/1.00  --time_out_prep_mult                    0.1
% 3.53/1.00  --splitting_mode                        input
% 3.53/1.00  --splitting_grd                         true
% 3.53/1.00  --splitting_cvd                         false
% 3.53/1.00  --splitting_cvd_svl                     false
% 3.53/1.00  --splitting_nvd                         32
% 3.53/1.00  --sub_typing                            true
% 3.53/1.00  --prep_gs_sim                           true
% 3.53/1.00  --prep_unflatten                        true
% 3.53/1.00  --prep_res_sim                          true
% 3.53/1.00  --prep_upred                            true
% 3.53/1.00  --prep_sem_filter                       exhaustive
% 3.53/1.00  --prep_sem_filter_out                   false
% 3.53/1.00  --pred_elim                             true
% 3.53/1.00  --res_sim_input                         true
% 3.53/1.00  --eq_ax_congr_red                       true
% 3.53/1.00  --pure_diseq_elim                       true
% 3.53/1.00  --brand_transform                       false
% 3.53/1.00  --non_eq_to_eq                          false
% 3.53/1.00  --prep_def_merge                        true
% 3.53/1.00  --prep_def_merge_prop_impl              false
% 3.53/1.00  --prep_def_merge_mbd                    true
% 3.53/1.00  --prep_def_merge_tr_red                 false
% 3.53/1.00  --prep_def_merge_tr_cl                  false
% 3.53/1.00  --smt_preprocessing                     true
% 3.53/1.00  --smt_ac_axioms                         fast
% 3.53/1.00  --preprocessed_out                      false
% 3.53/1.00  --preprocessed_stats                    false
% 3.53/1.00  
% 3.53/1.00  ------ Abstraction refinement Options
% 3.53/1.00  
% 3.53/1.00  --abstr_ref                             []
% 3.53/1.00  --abstr_ref_prep                        false
% 3.53/1.00  --abstr_ref_until_sat                   false
% 3.53/1.00  --abstr_ref_sig_restrict                funpre
% 3.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.00  --abstr_ref_under                       []
% 3.53/1.00  
% 3.53/1.00  ------ SAT Options
% 3.53/1.00  
% 3.53/1.00  --sat_mode                              false
% 3.53/1.00  --sat_fm_restart_options                ""
% 3.53/1.00  --sat_gr_def                            false
% 3.53/1.00  --sat_epr_types                         true
% 3.53/1.00  --sat_non_cyclic_types                  false
% 3.53/1.00  --sat_finite_models                     false
% 3.53/1.00  --sat_fm_lemmas                         false
% 3.53/1.00  --sat_fm_prep                           false
% 3.53/1.00  --sat_fm_uc_incr                        true
% 3.53/1.00  --sat_out_model                         small
% 3.53/1.00  --sat_out_clauses                       false
% 3.53/1.00  
% 3.53/1.00  ------ QBF Options
% 3.53/1.00  
% 3.53/1.00  --qbf_mode                              false
% 3.53/1.00  --qbf_elim_univ                         false
% 3.53/1.00  --qbf_dom_inst                          none
% 3.53/1.00  --qbf_dom_pre_inst                      false
% 3.53/1.00  --qbf_sk_in                             false
% 3.53/1.00  --qbf_pred_elim                         true
% 3.53/1.00  --qbf_split                             512
% 3.53/1.00  
% 3.53/1.00  ------ BMC1 Options
% 3.53/1.00  
% 3.53/1.00  --bmc1_incremental                      false
% 3.53/1.00  --bmc1_axioms                           reachable_all
% 3.53/1.00  --bmc1_min_bound                        0
% 3.53/1.00  --bmc1_max_bound                        -1
% 3.53/1.00  --bmc1_max_bound_default                -1
% 3.53/1.00  --bmc1_symbol_reachability              true
% 3.53/1.00  --bmc1_property_lemmas                  false
% 3.53/1.00  --bmc1_k_induction                      false
% 3.53/1.00  --bmc1_non_equiv_states                 false
% 3.53/1.00  --bmc1_deadlock                         false
% 3.53/1.00  --bmc1_ucm                              false
% 3.53/1.00  --bmc1_add_unsat_core                   none
% 3.53/1.00  --bmc1_unsat_core_children              false
% 3.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.00  --bmc1_out_stat                         full
% 3.53/1.00  --bmc1_ground_init                      false
% 3.53/1.00  --bmc1_pre_inst_next_state              false
% 3.53/1.00  --bmc1_pre_inst_state                   false
% 3.53/1.00  --bmc1_pre_inst_reach_state             false
% 3.53/1.00  --bmc1_out_unsat_core                   false
% 3.53/1.00  --bmc1_aig_witness_out                  false
% 3.53/1.00  --bmc1_verbose                          false
% 3.53/1.00  --bmc1_dump_clauses_tptp                false
% 3.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.00  --bmc1_dump_file                        -
% 3.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.00  --bmc1_ucm_extend_mode                  1
% 3.53/1.00  --bmc1_ucm_init_mode                    2
% 3.53/1.00  --bmc1_ucm_cone_mode                    none
% 3.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.00  --bmc1_ucm_relax_model                  4
% 3.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.00  --bmc1_ucm_layered_model                none
% 3.53/1.00  --bmc1_ucm_max_lemma_size               10
% 3.53/1.00  
% 3.53/1.00  ------ AIG Options
% 3.53/1.00  
% 3.53/1.00  --aig_mode                              false
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation Options
% 3.53/1.00  
% 3.53/1.00  --instantiation_flag                    true
% 3.53/1.00  --inst_sos_flag                         false
% 3.53/1.00  --inst_sos_phase                        true
% 3.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel_side                     none
% 3.53/1.00  --inst_solver_per_active                1400
% 3.53/1.00  --inst_solver_calls_frac                1.
% 3.53/1.00  --inst_passive_queue_type               priority_queues
% 3.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.00  --inst_passive_queues_freq              [25;2]
% 3.53/1.00  --inst_dismatching                      true
% 3.53/1.00  --inst_eager_unprocessed_to_passive     true
% 3.53/1.00  --inst_prop_sim_given                   true
% 3.53/1.00  --inst_prop_sim_new                     false
% 3.53/1.00  --inst_subs_new                         false
% 3.53/1.00  --inst_eq_res_simp                      false
% 3.53/1.00  --inst_subs_given                       false
% 3.53/1.00  --inst_orphan_elimination               true
% 3.53/1.00  --inst_learning_loop_flag               true
% 3.53/1.00  --inst_learning_start                   3000
% 3.53/1.00  --inst_learning_factor                  2
% 3.53/1.00  --inst_start_prop_sim_after_learn       3
% 3.53/1.00  --inst_sel_renew                        solver
% 3.53/1.00  --inst_lit_activity_flag                true
% 3.53/1.00  --inst_restr_to_given                   false
% 3.53/1.00  --inst_activity_threshold               500
% 3.53/1.00  --inst_out_proof                        true
% 3.53/1.00  
% 3.53/1.00  ------ Resolution Options
% 3.53/1.00  
% 3.53/1.00  --resolution_flag                       false
% 3.53/1.00  --res_lit_sel                           adaptive
% 3.53/1.00  --res_lit_sel_side                      none
% 3.53/1.00  --res_ordering                          kbo
% 3.53/1.00  --res_to_prop_solver                    active
% 3.53/1.00  --res_prop_simpl_new                    false
% 3.53/1.00  --res_prop_simpl_given                  true
% 3.53/1.00  --res_passive_queue_type                priority_queues
% 3.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.00  --res_passive_queues_freq               [15;5]
% 3.53/1.00  --res_forward_subs                      full
% 3.53/1.00  --res_backward_subs                     full
% 3.53/1.00  --res_forward_subs_resolution           true
% 3.53/1.00  --res_backward_subs_resolution          true
% 3.53/1.00  --res_orphan_elimination                true
% 3.53/1.00  --res_time_limit                        2.
% 3.53/1.00  --res_out_proof                         true
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Options
% 3.53/1.00  
% 3.53/1.00  --superposition_flag                    true
% 3.53/1.00  --sup_passive_queue_type                priority_queues
% 3.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.00  --demod_completeness_check              fast
% 3.53/1.00  --demod_use_ground                      true
% 3.53/1.00  --sup_to_prop_solver                    passive
% 3.53/1.00  --sup_prop_simpl_new                    true
% 3.53/1.00  --sup_prop_simpl_given                  true
% 3.53/1.00  --sup_fun_splitting                     false
% 3.53/1.00  --sup_smt_interval                      50000
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Simplification Setup
% 3.53/1.00  
% 3.53/1.00  --sup_indices_passive                   []
% 3.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_full_bw                           [BwDemod]
% 3.53/1.00  --sup_immed_triv                        [TrivRules]
% 3.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_immed_bw_main                     []
% 3.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/1.00  
% 3.53/1.00  ------ Combination Options
% 3.53/1.00  
% 3.53/1.00  --comb_res_mult                         3
% 3.53/1.00  --comb_sup_mult                         2
% 3.53/1.00  --comb_inst_mult                        10
% 3.53/1.00  
% 3.53/1.00  ------ Debug Options
% 3.53/1.00  
% 3.53/1.00  --dbg_backtrace                         false
% 3.53/1.00  --dbg_dump_prop_clauses                 false
% 3.53/1.00  --dbg_dump_prop_clauses_file            -
% 3.53/1.00  --dbg_out_stat                          false
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ Proving...
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS status Theorem for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  fof(f5,axiom,(
% 3.53/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f15,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f5])).
% 3.53/1.00  
% 3.53/1.00  fof(f16,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.53/1.00    inference(flattening,[],[f15])).
% 3.53/1.00  
% 3.53/1.00  fof(f31,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.53/1.00    inference(nnf_transformation,[],[f16])).
% 3.53/1.00  
% 3.53/1.00  fof(f32,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.53/1.00    inference(rectify,[],[f31])).
% 3.53/1.00  
% 3.53/1.00  fof(f35,plain,(
% 3.53/1.00    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f34,plain,(
% 3.53/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f33,plain,(
% 3.53/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f36,plain,(
% 3.53/1.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).
% 3.53/1.00  
% 3.53/1.00  fof(f51,plain,(
% 3.53/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f36])).
% 3.53/1.00  
% 3.53/1.00  fof(f76,plain,(
% 3.53/1.00    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f51])).
% 3.53/1.00  
% 3.53/1.00  fof(f11,conjecture,(
% 3.53/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f12,negated_conjecture,(
% 3.53/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.53/1.00    inference(negated_conjecture,[],[f11])).
% 3.53/1.00  
% 3.53/1.00  fof(f23,plain,(
% 3.53/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.53/1.00    inference(ennf_transformation,[],[f12])).
% 3.53/1.00  
% 3.53/1.00  fof(f24,plain,(
% 3.53/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.53/1.00    inference(flattening,[],[f23])).
% 3.53/1.00  
% 3.53/1.00  fof(f39,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f38,plain,(
% 3.53/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f40,plain,(
% 3.53/1.00    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f24,f39,f38])).
% 3.53/1.00  
% 3.53/1.00  fof(f68,plain,(
% 3.53/1.00    v1_funct_1(sK7)),
% 3.53/1.00    inference(cnf_transformation,[],[f40])).
% 3.53/1.00  
% 3.53/1.00  fof(f7,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f18,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f7])).
% 3.53/1.00  
% 3.53/1.00  fof(f59,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f18])).
% 3.53/1.00  
% 3.53/1.00  fof(f70,plain,(
% 3.53/1.00    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.53/1.00    inference(cnf_transformation,[],[f40])).
% 3.53/1.00  
% 3.53/1.00  fof(f69,plain,(
% 3.53/1.00    v1_funct_2(sK7,sK4,sK5)),
% 3.53/1.00    inference(cnf_transformation,[],[f40])).
% 3.53/1.00  
% 3.53/1.00  fof(f10,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f21,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f10])).
% 3.53/1.00  
% 3.53/1.00  fof(f22,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(flattening,[],[f21])).
% 3.53/1.00  
% 3.53/1.00  fof(f37,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(nnf_transformation,[],[f22])).
% 3.53/1.00  
% 3.53/1.00  fof(f62,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f37])).
% 3.53/1.00  
% 3.53/1.00  fof(f8,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f19,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f8])).
% 3.53/1.00  
% 3.53/1.00  fof(f60,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f19])).
% 3.53/1.00  
% 3.53/1.00  fof(f50,plain,(
% 3.53/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f36])).
% 3.53/1.00  
% 3.53/1.00  fof(f77,plain,(
% 3.53/1.00    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f50])).
% 3.53/1.00  
% 3.53/1.00  fof(f9,axiom,(
% 3.53/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f20,plain,(
% 3.53/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f9])).
% 3.53/1.00  
% 3.53/1.00  fof(f61,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f20])).
% 3.53/1.00  
% 3.53/1.00  fof(f71,plain,(
% 3.53/1.00    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.53/1.00    inference(cnf_transformation,[],[f40])).
% 3.53/1.00  
% 3.53/1.00  fof(f52,plain,(
% 3.53/1.00    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f36])).
% 3.53/1.00  
% 3.53/1.00  fof(f75,plain,(
% 3.53/1.00    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f72,plain,(
% 3.53/1.00    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f40])).
% 3.53/1.00  
% 3.53/1.00  fof(f4,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f14,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.53/1.00    inference(ennf_transformation,[],[f4])).
% 3.53/1.00  
% 3.53/1.00  fof(f27,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.53/1.00    inference(nnf_transformation,[],[f14])).
% 3.53/1.00  
% 3.53/1.00  fof(f28,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.53/1.00    inference(rectify,[],[f27])).
% 3.53/1.00  
% 3.53/1.00  fof(f29,plain,(
% 3.53/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f30,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.53/1.00  
% 3.53/1.00  fof(f47,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f30])).
% 3.53/1.00  
% 3.53/1.00  fof(f3,axiom,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f13,plain,(
% 3.53/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f3])).
% 3.53/1.00  
% 3.53/1.00  fof(f45,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f13])).
% 3.53/1.00  
% 3.53/1.00  fof(f2,axiom,(
% 3.53/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f25,plain,(
% 3.53/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.53/1.00    inference(nnf_transformation,[],[f2])).
% 3.53/1.00  
% 3.53/1.00  fof(f26,plain,(
% 3.53/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.53/1.00    inference(flattening,[],[f25])).
% 3.53/1.00  
% 3.53/1.00  fof(f43,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f26])).
% 3.53/1.00  
% 3.53/1.00  fof(f1,axiom,(
% 3.53/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f41,plain,(
% 3.53/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f1])).
% 3.53/1.00  
% 3.53/1.00  fof(f6,axiom,(
% 3.53/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f17,plain,(
% 3.53/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.53/1.00    inference(ennf_transformation,[],[f6])).
% 3.53/1.00  
% 3.53/1.00  fof(f58,plain,(
% 3.53/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f17])).
% 3.53/1.00  
% 3.53/1.00  cnf(c_15,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.53/1.00      | ~ v1_funct_1(X1)
% 3.53/1.00      | ~ v1_relat_1(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_31,negated_conjecture,
% 3.53/1.00      ( v1_funct_1(sK7) ),
% 3.53/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_663,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.53/1.00      | ~ v1_relat_1(X1)
% 3.53/1.00      | sK7 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_664,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.53/1.00      | r2_hidden(sK3(sK7,X1,X0),X1)
% 3.53/1.00      | ~ v1_relat_1(sK7) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_663]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1736,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 3.53/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_665,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 3.53/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1393,plain,( X0 = X0 ),theory(equality) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1952,plain,
% 3.53/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_1393]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_18,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | v1_relat_1(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_29,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_440,plain,
% 3.53/1.00      ( v1_relat_1(X0)
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.53/1.00      | sK7 != X0 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_441,plain,
% 3.53/1.00      ( v1_relat_1(sK7)
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_440]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1955,plain,
% 3.53/1.00      ( v1_relat_1(sK7)
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_441]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1956,plain,
% 3.53/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.53/1.00      | v1_relat_1(sK7) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1955]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2310,plain,
% 3.53/1.00      ( r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 3.53/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_1736,c_665,c_1952,c_1956]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2311,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_2310]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_30,negated_conjecture,
% 3.53/1.00      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.53/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_26,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.53/1.00      | k1_xboole_0 = X2 ),
% 3.53/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_386,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.53/1.00      | sK7 != X0
% 3.53/1.00      | k1_xboole_0 = X2 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_387,plain,
% 3.53/1.00      ( ~ v1_funct_2(sK7,X0,X1)
% 3.53/1.00      | k1_relset_1(X0,X1,sK7) = X0
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.53/1.00      | k1_xboole_0 = X1 ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_386]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_978,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,sK7) = X0
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.53/1.00      | sK5 != X1
% 3.53/1.00      | sK4 != X0
% 3.53/1.00      | sK7 != sK7
% 3.53/1.00      | k1_xboole_0 = X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_387]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_979,plain,
% 3.53/1.00      ( k1_relset_1(sK4,sK5,sK7) = sK4
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.53/1.00      | k1_xboole_0 = sK5 ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_978]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1052,plain,
% 3.53/1.00      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 3.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_979]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_19,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_431,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.53/1.00      | sK7 != X2 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_432,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,sK7) = k1_relat_1(sK7)
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_431]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1951,plain,
% 3.53/1.00      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.53/1.00      inference(equality_resolution,[status(thm)],[c_432]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2040,plain,
% 3.53/1.00      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_1052,c_1951]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_16,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.53/1.00      | ~ v1_funct_1(X1)
% 3.53/1.00      | ~ v1_relat_1(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_648,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.53/1.00      | ~ v1_relat_1(X1)
% 3.53/1.00      | sK7 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_649,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.53/1.00      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7))
% 3.53/1.00      | ~ v1_relat_1(sK7) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_648]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1737,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
% 3.53/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_650,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
% 3.53/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2384,plain,
% 3.53/1.00      ( r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
% 3.53/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_1737,c_650,c_1952,c_1956]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2385,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_2384]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2392,plain,
% 3.53/1.00      ( sK5 = k1_xboole_0
% 3.53/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2040,c_2385]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_20,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_422,plain,
% 3.53/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.53/1.00      | sK7 != X2 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_423,plain,
% 3.53/1.00      ( k7_relset_1(X0,X1,sK7,X2) = k9_relat_1(sK7,X2)
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_422]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1963,plain,
% 3.53/1.00      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.53/1.00      inference(equality_resolution,[status(thm)],[c_423]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_28,negated_conjecture,
% 3.53/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1746,plain,
% 3.53/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1990,plain,
% 3.53/1.00      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_1963,c_1746]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_14,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | ~ v1_funct_1(X1)
% 3.53/1.00      | ~ v1_relat_1(X1)
% 3.53/1.00      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_678,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | ~ v1_relat_1(X1)
% 3.53/1.00      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
% 3.53/1.00      | sK7 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_679,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.53/1.00      | ~ v1_relat_1(sK7)
% 3.53/1.00      | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_678]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1735,plain,
% 3.53/1.00      ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
% 3.53/1.00      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.53/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_680,plain,
% 3.53/1.00      ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
% 3.53/1.00      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.53/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2288,plain,
% 3.53/1.00      ( r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.53/1.00      | k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_1735,c_680,c_1952,c_1956]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2289,plain,
% 3.53/1.00      ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
% 3.53/1.00      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_2288]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2297,plain,
% 3.53/1.00      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1990,c_2289]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_27,negated_conjecture,
% 3.53/1.00      ( ~ r2_hidden(X0,sK4)
% 3.53/1.00      | ~ r2_hidden(X0,sK6)
% 3.53/1.00      | k1_funct_1(sK7,X0) != sK8 ),
% 3.53/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1747,plain,
% 3.53/1.00      ( k1_funct_1(sK7,X0) != sK8
% 3.53/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.53/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3225,plain,
% 3.53/1.00      ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
% 3.53/1.00      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2297,c_1747]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7890,plain,
% 3.53/1.00      ( sK5 = k1_xboole_0
% 3.53/1.00      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 3.53/1.00      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2392,c_3225]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9390,plain,
% 3.53/1.00      ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 3.53/1.00      | sK5 = k1_xboole_0 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_7890,c_1990]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9391,plain,
% 3.53/1.00      ( sK5 = k1_xboole_0
% 3.53/1.00      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_9390]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9396,plain,
% 3.53/1.00      ( sK5 = k1_xboole_0
% 3.53/1.00      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2311,c_9391]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9399,plain,
% 3.53/1.00      ( sK5 = k1_xboole_0 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_9396,c_1990]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.53/1.00      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.53/1.00      | ~ v1_relat_1(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1749,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.53/1.00      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.53/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.53/1.00      | ~ r2_hidden(X2,X0)
% 3.53/1.00      | r2_hidden(X2,X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_371,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,X1)
% 3.53/1.00      | r2_hidden(X0,X2)
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X2)
% 3.53/1.00      | sK7 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_372,plain,
% 3.53/1.00      ( r2_hidden(X0,X1)
% 3.53/1.00      | ~ r2_hidden(X0,sK7)
% 3.53/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X1) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_371]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1744,plain,
% 3.53/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0)
% 3.53/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.53/1.00      | r2_hidden(X1,sK7) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2259,plain,
% 3.53/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
% 3.53/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.53/1.00      inference(equality_resolution,[status(thm)],[c_1744]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2,plain,
% 3.53/1.00      ( r2_hidden(X0,X1)
% 3.53/1.00      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1753,plain,
% 3.53/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.53/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3364,plain,
% 3.53/1.00      ( r2_hidden(X0,sK5) = iProver_top
% 3.53/1.00      | r2_hidden(k4_tarski(X1,X0),sK7) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2259,c_1753]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3722,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(X0,sK5) = iProver_top
% 3.53/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1749,c_3364]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5409,plain,
% 3.53/1.00      ( r2_hidden(X0,sK5) = iProver_top
% 3.53/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_3722,c_1952,c_1956]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5410,plain,
% 3.53/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.53/1.00      | r2_hidden(X0,sK5) = iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_5409]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5423,plain,
% 3.53/1.00      ( r2_hidden(sK8,sK5) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1990,c_5410]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9404,plain,
% 3.53/1.00      ( r2_hidden(sK8,k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_9399,c_5423]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_0,plain,
% 3.53/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_360,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.53/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_361,plain,
% 3.53/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.53/1.00      inference(unflattening,[status(thm)],[c_360]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2103,plain,
% 3.53/1.00      ( ~ r2_hidden(sK8,k1_xboole_0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_361]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2106,plain,
% 3.53/1.00      ( r2_hidden(sK8,k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2103]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(contradiction,plain,
% 3.53/1.00      ( $false ),
% 3.53/1.00      inference(minisat,[status(thm)],[c_9404,c_2106]) ).
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  ------                               Statistics
% 3.53/1.00  
% 3.53/1.00  ------ General
% 3.53/1.00  
% 3.53/1.00  abstr_ref_over_cycles:                  0
% 3.53/1.00  abstr_ref_under_cycles:                 0
% 3.53/1.00  gc_basic_clause_elim:                   0
% 3.53/1.00  forced_gc_time:                         0
% 3.53/1.00  parsing_time:                           0.012
% 3.53/1.00  unif_index_cands_time:                  0.
% 3.53/1.00  unif_index_add_time:                    0.
% 3.53/1.00  orderings_time:                         0.
% 3.53/1.00  out_proof_time:                         0.009
% 3.53/1.00  total_time:                             0.258
% 3.53/1.00  num_of_symbols:                         55
% 3.53/1.00  num_of_terms:                           11907
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing
% 3.53/1.00  
% 3.53/1.00  num_of_splits:                          0
% 3.53/1.00  num_of_split_atoms:                     0
% 3.53/1.00  num_of_reused_defs:                     0
% 3.53/1.00  num_eq_ax_congr_red:                    42
% 3.53/1.00  num_of_sem_filtered_clauses:            1
% 3.53/1.00  num_of_subtypes:                        0
% 3.53/1.00  monotx_restored_types:                  0
% 3.53/1.00  sat_num_of_epr_types:                   0
% 3.53/1.00  sat_num_of_non_cyclic_types:            0
% 3.53/1.00  sat_guarded_non_collapsed_types:        0
% 3.53/1.00  num_pure_diseq_elim:                    0
% 3.53/1.00  simp_replaced_by:                       0
% 3.53/1.00  res_preprocessed:                       138
% 3.53/1.00  prep_upred:                             0
% 3.53/1.00  prep_unflattend:                        44
% 3.53/1.00  smt_new_axioms:                         0
% 3.53/1.00  pred_elim_cands:                        2
% 3.53/1.00  pred_elim:                              4
% 3.53/1.00  pred_elim_cl:                           7
% 3.53/1.00  pred_elim_cycles:                       7
% 3.53/1.00  merged_defs:                            0
% 3.53/1.00  merged_defs_ncl:                        0
% 3.53/1.00  bin_hyper_res:                          0
% 3.53/1.00  prep_cycles:                            4
% 3.53/1.00  pred_elim_time:                         0.011
% 3.53/1.00  splitting_time:                         0.
% 3.53/1.00  sem_filter_time:                        0.
% 3.53/1.00  monotx_time:                            0.
% 3.53/1.00  subtype_inf_time:                       0.
% 3.53/1.00  
% 3.53/1.00  ------ Problem properties
% 3.53/1.00  
% 3.53/1.00  clauses:                                25
% 3.53/1.00  conjectures:                            2
% 3.53/1.00  epr:                                    1
% 3.53/1.00  horn:                                   20
% 3.53/1.00  ground:                                 4
% 3.53/1.00  unary:                                  2
% 3.53/1.00  binary:                                 6
% 3.53/1.00  lits:                                   75
% 3.53/1.00  lits_eq:                                23
% 3.53/1.00  fd_pure:                                0
% 3.53/1.00  fd_pseudo:                              0
% 3.53/1.00  fd_cond:                                0
% 3.53/1.00  fd_pseudo_cond:                         4
% 3.53/1.00  ac_symbols:                             0
% 3.53/1.00  
% 3.53/1.00  ------ Propositional Solver
% 3.53/1.00  
% 3.53/1.00  prop_solver_calls:                      28
% 3.53/1.00  prop_fast_solver_calls:                 1208
% 3.53/1.00  smt_solver_calls:                       0
% 3.53/1.00  smt_fast_solver_calls:                  0
% 3.53/1.00  prop_num_of_clauses:                    3568
% 3.53/1.00  prop_preprocess_simplified:             8128
% 3.53/1.00  prop_fo_subsumed:                       15
% 3.53/1.00  prop_solver_time:                       0.
% 3.53/1.00  smt_solver_time:                        0.
% 3.53/1.00  smt_fast_solver_time:                   0.
% 3.53/1.00  prop_fast_solver_time:                  0.
% 3.53/1.00  prop_unsat_core_time:                   0.
% 3.53/1.00  
% 3.53/1.00  ------ QBF
% 3.53/1.00  
% 3.53/1.00  qbf_q_res:                              0
% 3.53/1.00  qbf_num_tautologies:                    0
% 3.53/1.00  qbf_prep_cycles:                        0
% 3.53/1.00  
% 3.53/1.00  ------ BMC1
% 3.53/1.00  
% 3.53/1.00  bmc1_current_bound:                     -1
% 3.53/1.00  bmc1_last_solved_bound:                 -1
% 3.53/1.00  bmc1_unsat_core_size:                   -1
% 3.53/1.00  bmc1_unsat_core_parents_size:           -1
% 3.53/1.00  bmc1_merge_next_fun:                    0
% 3.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation
% 3.53/1.00  
% 3.53/1.00  inst_num_of_clauses:                    772
% 3.53/1.00  inst_num_in_passive:                    379
% 3.53/1.00  inst_num_in_active:                     368
% 3.53/1.00  inst_num_in_unprocessed:                25
% 3.53/1.00  inst_num_of_loops:                      430
% 3.53/1.00  inst_num_of_learning_restarts:          0
% 3.53/1.00  inst_num_moves_active_passive:          58
% 3.53/1.00  inst_lit_activity:                      0
% 3.53/1.00  inst_lit_activity_moves:                0
% 3.53/1.00  inst_num_tautologies:                   0
% 3.53/1.00  inst_num_prop_implied:                  0
% 3.53/1.00  inst_num_existing_simplified:           0
% 3.53/1.00  inst_num_eq_res_simplified:             0
% 3.53/1.00  inst_num_child_elim:                    0
% 3.53/1.00  inst_num_of_dismatching_blockings:      105
% 3.53/1.00  inst_num_of_non_proper_insts:           663
% 3.53/1.00  inst_num_of_duplicates:                 0
% 3.53/1.00  inst_inst_num_from_inst_to_res:         0
% 3.53/1.00  inst_dismatching_checking_time:         0.
% 3.53/1.00  
% 3.53/1.00  ------ Resolution
% 3.53/1.00  
% 3.53/1.00  res_num_of_clauses:                     0
% 3.53/1.00  res_num_in_passive:                     0
% 3.53/1.00  res_num_in_active:                      0
% 3.53/1.00  res_num_of_loops:                       142
% 3.53/1.00  res_forward_subset_subsumed:            50
% 3.53/1.00  res_backward_subset_subsumed:           2
% 3.53/1.00  res_forward_subsumed:                   0
% 3.53/1.00  res_backward_subsumed:                  0
% 3.53/1.00  res_forward_subsumption_resolution:     0
% 3.53/1.00  res_backward_subsumption_resolution:    0
% 3.53/1.00  res_clause_to_clause_subsumption:       948
% 3.53/1.00  res_orphan_elimination:                 0
% 3.53/1.00  res_tautology_del:                      70
% 3.53/1.00  res_num_eq_res_simplified:              1
% 3.53/1.00  res_num_sel_changes:                    0
% 3.53/1.00  res_moves_from_active_to_pass:          0
% 3.53/1.00  
% 3.53/1.00  ------ Superposition
% 3.53/1.00  
% 3.53/1.00  sup_time_total:                         0.
% 3.53/1.00  sup_time_generating:                    0.
% 3.53/1.00  sup_time_sim_full:                      0.
% 3.53/1.00  sup_time_sim_immed:                     0.
% 3.53/1.00  
% 3.53/1.00  sup_num_of_clauses:                     360
% 3.53/1.00  sup_num_in_active:                      69
% 3.53/1.00  sup_num_in_passive:                     291
% 3.53/1.00  sup_num_of_loops:                       85
% 3.53/1.00  sup_fw_superposition:                   366
% 3.53/1.00  sup_bw_superposition:                   29
% 3.53/1.00  sup_immediate_simplified:               37
% 3.53/1.00  sup_given_eliminated:                   0
% 3.53/1.00  comparisons_done:                       0
% 3.53/1.00  comparisons_avoided:                    5
% 3.53/1.00  
% 3.53/1.00  ------ Simplifications
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  sim_fw_subset_subsumed:                 15
% 3.53/1.00  sim_bw_subset_subsumed:                 7
% 3.53/1.00  sim_fw_subsumed:                        19
% 3.53/1.00  sim_bw_subsumed:                        3
% 3.53/1.00  sim_fw_subsumption_res:                 0
% 3.53/1.00  sim_bw_subsumption_res:                 0
% 3.53/1.00  sim_tautology_del:                      3
% 3.53/1.00  sim_eq_tautology_del:                   0
% 3.53/1.00  sim_eq_res_simp:                        1
% 3.53/1.00  sim_fw_demodulated:                     1
% 3.53/1.00  sim_bw_demodulated:                     14
% 3.53/1.00  sim_light_normalised:                   0
% 3.53/1.00  sim_joinable_taut:                      0
% 3.53/1.00  sim_joinable_simp:                      0
% 3.53/1.00  sim_ac_normalised:                      0
% 3.53/1.00  sim_smt_subsumption:                    0
% 3.53/1.00  
%------------------------------------------------------------------------------

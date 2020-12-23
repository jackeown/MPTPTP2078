%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:57 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  160 (5534 expanded)
%              Number of clauses        :  100 (1730 expanded)
%              Number of leaves         :   20 (1423 expanded)
%              Depth                    :   35
%              Number of atoms          :  584 (30383 expanded)
%              Number of equality atoms :  279 (7794 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f21])).

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f36,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ r2_hidden(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f22,f35,f34])).

fof(f63,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f14,plain,(
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
    inference(flattening,[],[f14])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f9,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f19])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f61,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f65,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_755,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_764,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1382,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_755,c_764])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_756,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1690,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1382,c_756])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_768,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_758,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2066,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_755,c_758])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_765,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1240,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_755,c_765])).

cnf(c_2067,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2066,c_1240])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,plain,
    ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2212,plain,
    ( sK5 = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_30])).

cnf(c_2213,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2212])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_767,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2772,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2213,c_767])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1105,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK7) ),
    inference(resolution,[status(thm)],[c_1,c_26])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1126,plain,
    ( v1_relat_1(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1105,c_2])).

cnf(c_1127,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_3925,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2772,c_29,c_1127])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_769,plain,
    ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2975,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1690,c_769])).

cnf(c_3517,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2975,c_29,c_1127])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_757,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3521,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_757])).

cnf(c_3936,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3925,c_3521])).

cnf(c_3961,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3936,c_1690])).

cnf(c_3962,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3961])).

cnf(c_3967,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_3962])).

cnf(c_4107,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3967,c_29,c_1127,c_1690])).

cnf(c_4112,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4107,c_755])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_762,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4574,plain,
    ( sK4 = k1_xboole_0
    | sK7 = k1_xboole_0
    | v1_funct_2(sK7,sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4112,c_762])).

cnf(c_270,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_297,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_1227,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_283,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1148,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | X2 != sK5
    | X1 != sK4
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_1409,plain,
    ( v1_funct_2(sK7,X0,X1)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | X1 != sK5
    | X0 != sK4
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1647,plain,
    ( v1_funct_2(sK7,sK4,X0)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | X0 != sK5
    | sK4 != sK4
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_1649,plain,
    ( X0 != sK5
    | sK4 != sK4
    | sK7 != sK7
    | v1_funct_2(sK7,sK4,X0) = iProver_top
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1647])).

cnf(c_1651,plain,
    ( sK4 != sK4
    | sK7 != sK7
    | k1_xboole_0 != sK5
    | v1_funct_2(sK7,sK4,sK5) != iProver_top
    | v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_1648,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_271,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1990,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_1991,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1990])).

cnf(c_4746,plain,
    ( sK7 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4574,c_29,c_30,c_297,c_1127,c_1227,c_1651,c_1648,c_1690,c_1991,c_3967])).

cnf(c_4747,plain,
    ( sK4 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4746])).

cnf(c_4111,plain,
    ( k1_relset_1(sK4,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
    inference(demodulation,[status(thm)],[c_4107,c_1240])).

cnf(c_4751,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_relat_1(sK7)
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4747,c_4111])).

cnf(c_4752,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4747,c_4112])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_759,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4954,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
    | sK7 = k1_xboole_0
    | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4752,c_759])).

cnf(c_754,plain,
    ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4113,plain,
    ( v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4107,c_754])).

cnf(c_4753,plain,
    ( sK7 = k1_xboole_0
    | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4747,c_4113])).

cnf(c_5435,plain,
    ( sK7 = k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4954,c_4753])).

cnf(c_5436,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5435])).

cnf(c_5673,plain,
    ( k1_relat_1(sK7) = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4751,c_5436])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_775,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_766,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1920,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X1),sK0(X0,X2,X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_766])).

cnf(c_6017,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5673,c_1920])).

cnf(c_7794,plain,
    ( r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6017,c_1127])).

cnf(c_7795,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7794])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_781,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7803,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7795,c_781])).

cnf(c_7815,plain,
    ( sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1690,c_7803])).

cnf(c_8089,plain,
    ( r2_hidden(sK8,k9_relat_1(k1_xboole_0,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7815,c_1690])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_776,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2057,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(X1,k4_tarski(sK0(X0,X2,X1),X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_766])).

cnf(c_5130,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_2057])).

cnf(c_9069,plain,
    ( v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8089,c_5130])).

cnf(c_273,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1434,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK7)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_1435,plain,
    ( X0 != sK7
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1434])).

cnf(c_1437,plain,
    ( k1_xboole_0 != sK7
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_1219,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_1220,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9069,c_7815,c_1437,c_1220,c_1127,c_297])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:11:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.45/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.99  
% 3.45/0.99  ------  iProver source info
% 3.45/0.99  
% 3.45/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.99  git: non_committed_changes: false
% 3.45/0.99  git: last_make_outside_of_git: false
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  ------ Parsing...
% 3.45/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.99  ------ Proving...
% 3.45/0.99  ------ Problem Properties 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  clauses                                 29
% 3.45/0.99  conjectures                             5
% 3.45/0.99  EPR                                     4
% 3.45/0.99  Horn                                    22
% 3.45/0.99  unary                                   6
% 3.45/0.99  binary                                  3
% 3.45/0.99  lits                                    92
% 3.45/0.99  lits eq                                 19
% 3.45/0.99  fd_pure                                 0
% 3.45/0.99  fd_pseudo                               0
% 3.45/0.99  fd_cond                                 3
% 3.45/0.99  fd_pseudo_cond                          4
% 3.45/0.99  AC symbols                              0
% 3.45/0.99  
% 3.45/0.99  ------ Input Options Time Limit: Unbounded
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  Current options:
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ Proving...
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS status Theorem for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  fof(f10,conjecture,(
% 3.45/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f11,negated_conjecture,(
% 3.45/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.45/0.99    inference(negated_conjecture,[],[f10])).
% 3.45/0.99  
% 3.45/0.99  fof(f21,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.45/0.99    inference(ennf_transformation,[],[f11])).
% 3.45/0.99  
% 3.45/0.99  fof(f22,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.45/0.99    inference(flattening,[],[f21])).
% 3.45/0.99  
% 3.45/0.99  fof(f35,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f34,plain,(
% 3.45/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f36,plain,(
% 3.45/0.99    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f22,f35,f34])).
% 3.45/0.99  
% 3.45/0.99  fof(f63,plain,(
% 3.45/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.45/0.99    inference(cnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f8,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f18,plain,(
% 3.45/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f8])).
% 3.45/0.99  
% 3.45/0.99  fof(f54,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f18])).
% 3.45/0.99  
% 3.45/0.99  fof(f64,plain,(
% 3.45/0.99    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.45/0.99    inference(cnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f5,axiom,(
% 3.45/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f14,plain,(
% 3.45/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f5])).
% 3.45/0.99  
% 3.45/0.99  fof(f15,plain,(
% 3.45/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(flattening,[],[f14])).
% 3.45/0.99  
% 3.45/0.99  fof(f27,plain,(
% 3.45/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(nnf_transformation,[],[f15])).
% 3.45/0.99  
% 3.45/0.99  fof(f28,plain,(
% 3.45/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(rectify,[],[f27])).
% 3.45/0.99  
% 3.45/0.99  fof(f31,plain,(
% 3.45/0.99    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f30,plain,(
% 3.45/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f29,plain,(
% 3.45/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f32,plain,(
% 3.45/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).
% 3.45/0.99  
% 3.45/0.99  fof(f45,plain,(
% 3.45/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f32])).
% 3.45/0.99  
% 3.45/0.99  fof(f69,plain,(
% 3.45/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(equality_resolution,[],[f45])).
% 3.45/0.99  
% 3.45/0.99  fof(f9,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f19,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f9])).
% 3.45/0.99  
% 3.45/0.99  fof(f20,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(flattening,[],[f19])).
% 3.45/0.99  
% 3.45/0.99  fof(f33,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(nnf_transformation,[],[f20])).
% 3.45/0.99  
% 3.45/0.99  fof(f55,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f33])).
% 3.45/0.99  
% 3.45/0.99  fof(f7,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f17,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/0.99    inference(ennf_transformation,[],[f7])).
% 3.45/0.99  
% 3.45/0.99  fof(f53,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f17])).
% 3.45/0.99  
% 3.45/0.99  fof(f62,plain,(
% 3.45/0.99    v1_funct_2(sK7,sK4,sK5)),
% 3.45/0.99    inference(cnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f44,plain,(
% 3.45/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f32])).
% 3.45/0.99  
% 3.45/0.99  fof(f70,plain,(
% 3.45/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(equality_resolution,[],[f44])).
% 3.45/0.99  
% 3.45/0.99  fof(f61,plain,(
% 3.45/0.99    v1_funct_1(sK7)),
% 3.45/0.99    inference(cnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f2,axiom,(
% 3.45/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f12,plain,(
% 3.45/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.45/0.99    inference(ennf_transformation,[],[f2])).
% 3.45/0.99  
% 3.45/0.99  fof(f38,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f12])).
% 3.45/0.99  
% 3.45/0.99  fof(f3,axiom,(
% 3.45/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f39,plain,(
% 3.45/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f3])).
% 3.45/0.99  
% 3.45/0.99  fof(f46,plain,(
% 3.45/0.99    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f32])).
% 3.45/0.99  
% 3.45/0.99  fof(f68,plain,(
% 3.45/0.99    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/0.99    inference(equality_resolution,[],[f46])).
% 3.45/0.99  
% 3.45/0.99  fof(f65,plain,(
% 3.45/0.99    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f36])).
% 3.45/0.99  
% 3.45/0.99  fof(f59,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f33])).
% 3.45/0.99  
% 3.45/0.99  fof(f73,plain,(
% 3.45/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.45/0.99    inference(equality_resolution,[],[f59])).
% 3.45/0.99  
% 3.45/0.99  fof(f56,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f33])).
% 3.45/0.99  
% 3.45/0.99  fof(f75,plain,(
% 3.45/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.45/0.99    inference(equality_resolution,[],[f56])).
% 3.45/0.99  
% 3.45/0.99  fof(f4,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f13,plain,(
% 3.45/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(ennf_transformation,[],[f4])).
% 3.45/0.99  
% 3.45/0.99  fof(f23,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(nnf_transformation,[],[f13])).
% 3.45/0.99  
% 3.45/0.99  fof(f24,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(rectify,[],[f23])).
% 3.45/0.99  
% 3.45/0.99  fof(f25,plain,(
% 3.45/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f26,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.45/0.99  
% 3.45/0.99  fof(f40,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  fof(f6,axiom,(
% 3.45/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f16,plain,(
% 3.45/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f6])).
% 3.45/0.99  
% 3.45/0.99  fof(f52,plain,(
% 3.45/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f16])).
% 3.45/0.99  
% 3.45/0.99  fof(f1,axiom,(
% 3.45/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f37,plain,(
% 3.45/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f1])).
% 3.45/0.99  
% 3.45/0.99  fof(f41,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  cnf(c_26,negated_conjecture,
% 3.45/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.45/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_755,plain,
% 3.45/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_17,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.45/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_764,plain,
% 3.45/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1382,plain,
% 3.45/0.99      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_755,c_764]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_25,negated_conjecture,
% 3.45/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_756,plain,
% 3.45/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1690,plain,
% 3.45/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_1382,c_756]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_13,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.45/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.45/0.99      | ~ v1_funct_1(X1)
% 3.45/0.99      | ~ v1_relat_1(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_768,plain,
% 3.45/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
% 3.45/0.99      | v1_funct_1(X1) != iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_23,plain,
% 3.45/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.45/0.99      | k1_xboole_0 = X2 ),
% 3.45/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_758,plain,
% 3.45/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.45/0.99      | k1_xboole_0 = X1
% 3.45/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2066,plain,
% 3.45/0.99      ( k1_relset_1(sK4,sK5,sK7) = sK4
% 3.45/0.99      | sK5 = k1_xboole_0
% 3.45/0.99      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_755,c_758]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_16,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_765,plain,
% 3.45/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.45/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1240,plain,
% 3.45/0.99      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_755,c_765]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2067,plain,
% 3.45/0.99      ( k1_relat_1(sK7) = sK4
% 3.45/0.99      | sK5 = k1_xboole_0
% 3.45/0.99      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_2066,c_1240]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_27,negated_conjecture,
% 3.45/0.99      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.45/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_30,plain,
% 3.45/0.99      ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2212,plain,
% 3.45/0.99      ( sK5 = k1_xboole_0 | k1_relat_1(sK7) = sK4 ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_2067,c_30]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2213,plain,
% 3.45/0.99      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_2212]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_14,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.45/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.45/0.99      | ~ v1_funct_1(X1)
% 3.45/0.99      | ~ v1_relat_1(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_767,plain,
% 3.45/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 3.45/0.99      | v1_funct_1(X1) != iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2772,plain,
% 3.45/0.99      ( sK5 = k1_xboole_0
% 3.45/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.45/0.99      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
% 3.45/0.99      | v1_funct_1(sK7) != iProver_top
% 3.45/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2213,c_767]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_28,negated_conjecture,
% 3.45/0.99      ( v1_funct_1(sK7) ),
% 3.45/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_29,plain,
% 3.45/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1,plain,
% 3.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.45/0.99      | ~ v1_relat_1(X1)
% 3.45/0.99      | v1_relat_1(X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1105,plain,
% 3.45/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) | v1_relat_1(sK7) ),
% 3.45/0.99      inference(resolution,[status(thm)],[c_1,c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2,plain,
% 3.45/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.45/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1126,plain,
% 3.45/0.99      ( v1_relat_1(sK7) ),
% 3.45/0.99      inference(forward_subsumption_resolution,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_1105,c_2]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1127,plain,
% 3.45/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3925,plain,
% 3.45/0.99      ( sK5 = k1_xboole_0
% 3.45/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.45/0.99      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_2772,c_29,c_1127]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_12,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.45/0.99      | ~ v1_funct_1(X1)
% 3.45/0.99      | ~ v1_relat_1(X1)
% 3.45/0.99      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 3.45/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_769,plain,
% 3.45/0.99      ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
% 3.45/0.99      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 3.45/0.99      | v1_funct_1(X0) != iProver_top
% 3.45/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2975,plain,
% 3.45/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
% 3.45/0.99      | v1_funct_1(sK7) != iProver_top
% 3.45/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1690,c_769]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3517,plain,
% 3.45/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_2975,c_29,c_1127]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_24,negated_conjecture,
% 3.45/0.99      ( ~ r2_hidden(X0,sK4)
% 3.45/0.99      | ~ r2_hidden(X0,sK6)
% 3.45/0.99      | k1_funct_1(sK7,X0) != sK8 ),
% 3.45/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_757,plain,
% 3.45/0.99      ( k1_funct_1(sK7,X0) != sK8
% 3.45/0.99      | r2_hidden(X0,sK4) != iProver_top
% 3.45/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3521,plain,
% 3.45/0.99      ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
% 3.45/0.99      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_3517,c_757]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3936,plain,
% 3.45/0.99      ( sK5 = k1_xboole_0
% 3.45/0.99      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 3.45/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_3925,c_3521]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3961,plain,
% 3.45/0.99      ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 3.45/0.99      | sK5 = k1_xboole_0 ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_3936,c_1690]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3962,plain,
% 3.45/0.99      ( sK5 = k1_xboole_0
% 3.45/0.99      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_3961]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3967,plain,
% 3.45/0.99      ( sK5 = k1_xboole_0
% 3.45/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.45/0.99      | v1_funct_1(sK7) != iProver_top
% 3.45/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_768,c_3962]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4107,plain,
% 3.45/0.99      ( sK5 = k1_xboole_0 ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_3967,c_29,c_1127,c_1690]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4112,plain,
% 3.45/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_4107,c_755]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_19,plain,
% 3.45/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.45/0.99      | k1_xboole_0 = X1
% 3.45/0.99      | k1_xboole_0 = X0 ),
% 3.45/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_762,plain,
% 3.45/0.99      ( k1_xboole_0 = X0
% 3.45/0.99      | k1_xboole_0 = X1
% 3.45/0.99      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.45/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4574,plain,
% 3.45/0.99      ( sK4 = k1_xboole_0
% 3.45/0.99      | sK7 = k1_xboole_0
% 3.45/0.99      | v1_funct_2(sK7,sK4,k1_xboole_0) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4112,c_762]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_270,plain,( X0 = X0 ),theory(equality) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_297,plain,
% 3.45/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_270]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1227,plain,
% 3.45/0.99      ( sK7 = sK7 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_270]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_283,plain,
% 3.45/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.45/0.99      | v1_funct_2(X3,X4,X5)
% 3.45/0.99      | X3 != X0
% 3.45/0.99      | X4 != X1
% 3.45/0.99      | X5 != X2 ),
% 3.45/0.99      theory(equality) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1148,plain,
% 3.45/0.99      ( v1_funct_2(X0,X1,X2)
% 3.45/0.99      | ~ v1_funct_2(sK7,sK4,sK5)
% 3.45/0.99      | X2 != sK5
% 3.45/0.99      | X1 != sK4
% 3.45/0.99      | X0 != sK7 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_283]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1409,plain,
% 3.45/0.99      ( v1_funct_2(sK7,X0,X1)
% 3.45/0.99      | ~ v1_funct_2(sK7,sK4,sK5)
% 3.45/0.99      | X1 != sK5
% 3.45/0.99      | X0 != sK4
% 3.45/0.99      | sK7 != sK7 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1148]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1647,plain,
% 3.45/0.99      ( v1_funct_2(sK7,sK4,X0)
% 3.45/0.99      | ~ v1_funct_2(sK7,sK4,sK5)
% 3.45/0.99      | X0 != sK5
% 3.45/0.99      | sK4 != sK4
% 3.45/0.99      | sK7 != sK7 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1409]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1649,plain,
% 3.45/0.99      ( X0 != sK5
% 3.45/0.99      | sK4 != sK4
% 3.45/0.99      | sK7 != sK7
% 3.45/0.99      | v1_funct_2(sK7,sK4,X0) = iProver_top
% 3.45/0.99      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1647]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1651,plain,
% 3.45/0.99      ( sK4 != sK4
% 3.45/0.99      | sK7 != sK7
% 3.45/0.99      | k1_xboole_0 != sK5
% 3.45/0.99      | v1_funct_2(sK7,sK4,sK5) != iProver_top
% 3.45/0.99      | v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1649]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1648,plain,
% 3.45/0.99      ( sK4 = sK4 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_270]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_271,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1990,plain,
% 3.45/0.99      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_271]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1991,plain,
% 3.45/0.99      ( sK5 != k1_xboole_0
% 3.45/0.99      | k1_xboole_0 = sK5
% 3.45/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1990]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4746,plain,
% 3.45/0.99      ( sK7 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_4574,c_29,c_30,c_297,c_1127,c_1227,c_1651,c_1648,
% 3.45/0.99                 c_1690,c_1991,c_3967]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4747,plain,
% 3.45/0.99      ( sK4 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_4746]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4111,plain,
% 3.45/0.99      ( k1_relset_1(sK4,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_4107,c_1240]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4751,plain,
% 3.45/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_relat_1(sK7)
% 3.45/0.99      | sK7 = k1_xboole_0 ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4747,c_4111]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4752,plain,
% 3.45/0.99      ( sK7 = k1_xboole_0
% 3.45/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4747,c_4112]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_22,plain,
% 3.45/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.45/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.45/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_759,plain,
% 3.45/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.45/0.99      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 3.45/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4954,plain,
% 3.45/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
% 3.45/0.99      | sK7 = k1_xboole_0
% 3.45/0.99      | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4752,c_759]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_754,plain,
% 3.45/0.99      ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4113,plain,
% 3.45/0.99      ( v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_4107,c_754]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_4753,plain,
% 3.45/0.99      ( sK7 = k1_xboole_0
% 3.45/0.99      | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4747,c_4113]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5435,plain,
% 3.45/0.99      ( sK7 = k1_xboole_0
% 3.45/0.99      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0 ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_4954,c_4753]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5436,plain,
% 3.45/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
% 3.45/0.99      | sK7 = k1_xboole_0 ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_5435]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5673,plain,
% 3.45/0.99      ( k1_relat_1(sK7) = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_4751,c_5436]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.45/0.99      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 3.45/0.99      | ~ v1_relat_1(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_775,plain,
% 3.45/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_15,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_766,plain,
% 3.45/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.45/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1920,plain,
% 3.45/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r1_tarski(k1_relat_1(X1),sK0(X0,X2,X1)) != iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_775,c_766]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6017,plain,
% 3.45/0.99      ( sK7 = k1_xboole_0
% 3.45/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.45/0.99      | r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top
% 3.45/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_5673,c_1920]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7794,plain,
% 3.45/0.99      ( r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top
% 3.45/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.45/0.99      | sK7 = k1_xboole_0 ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_6017,c_1127]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7795,plain,
% 3.45/0.99      ( sK7 = k1_xboole_0
% 3.45/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.45/0.99      | r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top ),
% 3.45/0.99      inference(renaming,[status(thm)],[c_7794]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_0,plain,
% 3.45/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_781,plain,
% 3.45/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7803,plain,
% 3.45/0.99      ( sK7 = k1_xboole_0
% 3.45/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.45/0.99      inference(forward_subsumption_resolution,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_7795,c_781]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7815,plain,
% 3.45/0.99      ( sK7 = k1_xboole_0 ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_1690,c_7803]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_8089,plain,
% 3.45/0.99      ( r2_hidden(sK8,k9_relat_1(k1_xboole_0,sK6)) = iProver_top ),
% 3.45/0.99      inference(demodulation,[status(thm)],[c_7815,c_1690]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5,plain,
% 3.45/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.45/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.45/0.99      | ~ v1_relat_1(X1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_776,plain,
% 3.45/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2057,plain,
% 3.45/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.45/0.99      | r1_tarski(X1,k4_tarski(sK0(X0,X2,X1),X0)) != iProver_top
% 3.45/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_776,c_766]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5130,plain,
% 3.45/0.99      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
% 3.45/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_781,c_2057]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9069,plain,
% 3.45/0.99      ( v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_8089,c_5130]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_273,plain,
% 3.45/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.45/0.99      theory(equality) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1434,plain,
% 3.45/0.99      ( v1_relat_1(X0) | ~ v1_relat_1(sK7) | X0 != sK7 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_273]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1435,plain,
% 3.45/0.99      ( X0 != sK7
% 3.45/0.99      | v1_relat_1(X0) = iProver_top
% 3.45/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_1434]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1437,plain,
% 3.45/0.99      ( k1_xboole_0 != sK7
% 3.45/0.99      | v1_relat_1(sK7) != iProver_top
% 3.45/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1435]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1219,plain,
% 3.45/0.99      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_271]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1220,plain,
% 3.45/0.99      ( sK7 != k1_xboole_0
% 3.45/0.99      | k1_xboole_0 = sK7
% 3.45/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_1219]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(contradiction,plain,
% 3.45/0.99      ( $false ),
% 3.45/0.99      inference(minisat,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_9069,c_7815,c_1437,c_1220,c_1127,c_297]) ).
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  ------                               Statistics
% 3.45/0.99  
% 3.45/0.99  ------ Selected
% 3.45/0.99  
% 3.45/0.99  total_time:                             0.341
% 3.45/0.99  
%------------------------------------------------------------------------------

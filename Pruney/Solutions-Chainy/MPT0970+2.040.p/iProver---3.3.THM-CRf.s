%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:53 EST 2020

% Result     : Theorem 8.17s
% Output     : CNFRefutation 8.17s
% Verified   : 
% Statistics : Number of formulae       :  196 (2915 expanded)
%              Number of clauses        :  119 ( 916 expanded)
%              Number of leaves         :   20 ( 711 expanded)
%              Depth                    :   34
%              Number of atoms          :  731 (14768 expanded)
%              Number of equality atoms :  388 (5181 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f55,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK9(X3)) = X3
        & r2_hidden(sK9(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK6,sK7,sK8) != sK7
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK8,X4) = X3
              & r2_hidden(X4,sK6) )
          | ~ r2_hidden(X3,sK7) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK8,sK6,sK7)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( k2_relset_1(sK6,sK7,sK8) != sK7
    & ! [X3] :
        ( ( k1_funct_1(sK8,sK9(X3)) = X3
          & r2_hidden(sK9(X3),sK6) )
        | ~ r2_hidden(X3,sK7) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK8,sK6,sK7)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f32,f55,f54])).

fof(f96,plain,(
    v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f56])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f97,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f46,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    k2_relset_1(sK6,sK7,sK8) != sK7 ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f48])).

fof(f51,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
        & r2_hidden(sK5(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
     => r2_hidden(k4_tarski(sK4(X2,X3),X3),X2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(sK4(X2,X3),X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
            & r2_hidden(sK5(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f49,f51,f50])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK5(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f98,plain,(
    ! [X3] :
      ( r2_hidden(sK9(X3),sK6)
      | ~ r2_hidden(X3,sK7) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    ! [X3] :
      ( k1_funct_1(sK8,sK9(X3)) = X3
      | ~ r2_hidden(X3,sK7) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f78,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f106,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f105])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f104,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f61])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f103,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f62])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f112,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_483,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_41])).

cnf(c_484,plain,
    ( ~ v1_funct_2(sK8,X0,X1)
    | k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_891,plain,
    ( k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != sK8
    | sK7 != X1
    | sK6 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_484])).

cnf(c_892,plain,
    ( k1_relset_1(sK6,sK7,sK8) = sK6
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = sK7 ),
    inference(unflattening,[status(thm)],[c_891])).

cnf(c_969,plain,
    ( k1_relset_1(sK6,sK7,sK8) = sK6
    | k1_xboole_0 = sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_892])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_528,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_41])).

cnf(c_529,plain,
    ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_12487,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
    inference(equality_resolution,[status(thm)],[c_529])).

cnf(c_12529,plain,
    ( k1_relat_1(sK8) = sK6
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_969,c_12487])).

cnf(c_21,plain,
    ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_703,plain,
    ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_43])).

cnf(c_704,plain,
    ( r2_hidden(sK2(sK8,X0,X1),k1_relat_1(sK8))
    | r2_hidden(sK1(sK8,X0,X1),X1)
    | ~ v1_relat_1(sK8)
    | k9_relat_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_12217,plain,
    ( k9_relat_1(sK8,X0) = X1
    | r2_hidden(sK2(sK8,X0,X1),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_13032,plain,
    ( k9_relat_1(sK8,X0) = X1
    | sK7 = k1_xboole_0
    | r2_hidden(sK2(sK8,X0,X1),sK6) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_12529,c_12217])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_519,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_41])).

cnf(c_520,plain,
    ( k2_relset_1(X0,X1,sK8) = k2_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_12484,plain,
    ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
    inference(equality_resolution,[status(thm)],[c_520])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK6,sK7,sK8) != sK7 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_12492,plain,
    ( k2_relat_1(sK8) != sK7 ),
    inference(demodulation,[status(thm)],[c_12484,c_38])).

cnf(c_31,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | k2_relset_1(X2,X0,X1) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_570,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | k2_relset_1(X2,X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_41])).

cnf(c_571,plain,
    ( r2_hidden(sK5(X0,sK8),X0)
    | k2_relset_1(X1,X0,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_12218,plain,
    ( k2_relset_1(X0,X1,sK8) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(sK5(X1,sK8),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_12865,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_12218])).

cnf(c_12868,plain,
    ( k2_relat_1(sK8) = sK7
    | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12865,c_12484])).

cnf(c_40,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(sK9(X0),sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_13197,plain,
    ( ~ r2_hidden(sK5(sK7,sK8),sK7)
    | r2_hidden(sK9(sK5(sK7,sK8)),sK6) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_13201,plain,
    ( r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
    | r2_hidden(sK9(sK5(sK7,sK8)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13197])).

cnf(c_16129,plain,
    ( r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12868,c_12492])).

cnf(c_39,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,sK9(X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_12227,plain,
    ( k1_funct_1(sK8,sK9(X0)) = X0
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_16134,plain,
    ( k1_funct_1(sK8,sK9(sK5(sK7,sK8))) = sK5(sK7,sK8) ),
    inference(superposition,[status(thm)],[c_16129,c_12227])).

cnf(c_12226,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK9(X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_757,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_43])).

cnf(c_758,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_12214,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_12230,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12231,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_12233,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13739,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
    | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12231,c_12233])).

cnf(c_119,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17558,plain,
    ( r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
    | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
    | r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13739,c_119])).

cnf(c_17559,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
    | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_17558])).

cnf(c_17567,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k9_relat_1(X1,k1_relat_1(X1))) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12230,c_17559])).

cnf(c_17611,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_12214,c_17567])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_453,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_41])).

cnf(c_454,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_12222,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_12603,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_12222])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_12234,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_13216,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12603,c_12234])).

cnf(c_17916,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17611,c_13216])).

cnf(c_17917,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top ),
    inference(renaming,[status(thm)],[c_17916])).

cnf(c_17928,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK9(X0)),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | r2_hidden(sK9(X0),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12226,c_17917])).

cnf(c_18137,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
    | r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16134,c_17928])).

cnf(c_18229,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18137,c_12492,c_12868])).

cnf(c_30,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(X1,X2)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | k2_relset_1(X3,X1,X2) = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_537,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(X1,X2)),X2)
    | k2_relset_1(X3,X1,X2) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_538,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(X1,sK8)),sK8)
    | k2_relset_1(X2,X1,sK8) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_12220,plain,
    ( k2_relset_1(X0,X1,sK8) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(k4_tarski(X2,sK5(X1,sK8)),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_12731,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_12220])).

cnf(c_12734,plain,
    ( k2_relat_1(sK8) = sK7
    | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12731,c_12484])).

cnf(c_13452,plain,
    ( r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12734,c_12492])).

cnf(c_13657,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_12231,c_13452])).

cnf(c_14829,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13657,c_13216])).

cnf(c_18235,plain,
    ( r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18229,c_14829])).

cnf(c_18237,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK9(sK5(sK7,sK8)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12529,c_18235])).

cnf(c_28851,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13032,c_12492,c_12868,c_13201,c_18237])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_620,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_41])).

cnf(c_621,plain,
    ( ~ v1_funct_2(sK8,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_916,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != sK8
    | sK7 != X0
    | sK6 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_621])).

cnf(c_917,plain,
    ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK6 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_12316,plain,
    ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_917,c_4])).

cnf(c_28919,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28851,c_12316])).

cnf(c_12581,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_529])).

cnf(c_28922,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_28851,c_12581])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_28968,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_28922,c_3])).

cnf(c_28969,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8) ),
    inference(equality_resolution_simp,[status(thm)],[c_28968])).

cnf(c_28976,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28919,c_28969])).

cnf(c_28980,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28976,c_3])).

cnf(c_28981,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_28980])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_602,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_41])).

cnf(c_603,plain,
    ( ~ v1_funct_2(sK8,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK8 ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_902,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != sK8
    | sK8 = k1_xboole_0
    | sK7 != k1_xboole_0
    | sK6 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_603])).

cnf(c_903,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 = k1_xboole_0
    | sK7 != k1_xboole_0
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_902])).

cnf(c_12324,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k1_xboole_0)
    | sK8 = k1_xboole_0
    | sK7 != k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_903,c_3])).

cnf(c_28914,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK8 = k1_xboole_0
    | sK6 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28851,c_12324])).

cnf(c_29013,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK8 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_28914])).

cnf(c_29017,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK8 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29013,c_3])).

cnf(c_29018,plain,
    ( sK8 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_29017])).

cnf(c_28926,plain,
    ( k2_relat_1(sK8) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28851,c_12492])).

cnf(c_33453,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_29018,c_28926])).

cnf(c_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34096,plain,
    ( sK6 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_33453,c_14])).

cnf(c_34097,plain,
    ( sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_34096])).

cnf(c_34814,plain,
    ( k1_relat_1(sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28981,c_34097])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12228,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_35328,plain,
    ( sK8 = k1_xboole_0
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_34814,c_12228])).

cnf(c_35380,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35328,c_13216])).

cnf(c_35402,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35380,c_28926])).

cnf(c_35579,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_35402,c_14])).

cnf(c_35580,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_35579])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:12:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.17/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.17/1.50  
% 8.17/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.17/1.50  
% 8.17/1.50  ------  iProver source info
% 8.17/1.50  
% 8.17/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.17/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.17/1.50  git: non_committed_changes: false
% 8.17/1.50  git: last_make_outside_of_git: false
% 8.17/1.50  
% 8.17/1.50  ------ 
% 8.17/1.50  ------ Parsing...
% 8.17/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  ------ Proving...
% 8.17/1.50  ------ Problem Properties 
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  clauses                                 35
% 8.17/1.50  conjectures                             3
% 8.17/1.50  EPR                                     2
% 8.17/1.50  Horn                                    28
% 8.17/1.50  unary                                   7
% 8.17/1.50  binary                                  5
% 8.17/1.50  lits                                    97
% 8.17/1.50  lits eq                                 42
% 8.17/1.50  fd_pure                                 0
% 8.17/1.50  fd_pseudo                               0
% 8.17/1.50  fd_cond                                 3
% 8.17/1.50  fd_pseudo_cond                          5
% 8.17/1.50  AC symbols                              0
% 8.17/1.50  
% 8.17/1.50  ------ Input Options Time Limit: Unbounded
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 8.17/1.50  Current options:
% 8.17/1.50  ------ 
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.17/1.50  
% 8.17/1.50  ------ Proving...
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  % SZS status Theorem for theBenchmark.p
% 8.17/1.50  
% 8.17/1.50   Resolution empty clause
% 8.17/1.50  
% 8.17/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.17/1.50  
% 8.17/1.50  fof(f15,conjecture,(
% 8.17/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f16,negated_conjecture,(
% 8.17/1.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 8.17/1.50    inference(negated_conjecture,[],[f15])).
% 8.17/1.50  
% 8.17/1.50  fof(f31,plain,(
% 8.17/1.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 8.17/1.50    inference(ennf_transformation,[],[f16])).
% 8.17/1.50  
% 8.17/1.50  fof(f32,plain,(
% 8.17/1.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 8.17/1.50    inference(flattening,[],[f31])).
% 8.17/1.50  
% 8.17/1.50  fof(f55,plain,(
% 8.17/1.50    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK9(X3)) = X3 & r2_hidden(sK9(X3),X0)))) )),
% 8.17/1.50    introduced(choice_axiom,[])).
% 8.17/1.50  
% 8.17/1.50  fof(f54,plain,(
% 8.17/1.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK6,sK7,sK8) != sK7 & ! [X3] : (? [X4] : (k1_funct_1(sK8,X4) = X3 & r2_hidden(X4,sK6)) | ~r2_hidden(X3,sK7)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8))),
% 8.17/1.50    introduced(choice_axiom,[])).
% 8.17/1.50  
% 8.17/1.50  fof(f56,plain,(
% 8.17/1.50    k2_relset_1(sK6,sK7,sK8) != sK7 & ! [X3] : ((k1_funct_1(sK8,sK9(X3)) = X3 & r2_hidden(sK9(X3),sK6)) | ~r2_hidden(X3,sK7)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8)),
% 8.17/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f32,f55,f54])).
% 8.17/1.50  
% 8.17/1.50  fof(f96,plain,(
% 8.17/1.50    v1_funct_2(sK8,sK6,sK7)),
% 8.17/1.50    inference(cnf_transformation,[],[f56])).
% 8.17/1.50  
% 8.17/1.50  fof(f14,axiom,(
% 8.17/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f29,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.17/1.50    inference(ennf_transformation,[],[f14])).
% 8.17/1.50  
% 8.17/1.50  fof(f30,plain,(
% 8.17/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.17/1.50    inference(flattening,[],[f29])).
% 8.17/1.50  
% 8.17/1.50  fof(f53,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.17/1.50    inference(nnf_transformation,[],[f30])).
% 8.17/1.50  
% 8.17/1.50  fof(f89,plain,(
% 8.17/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.17/1.50    inference(cnf_transformation,[],[f53])).
% 8.17/1.50  
% 8.17/1.50  fof(f97,plain,(
% 8.17/1.50    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 8.17/1.50    inference(cnf_transformation,[],[f56])).
% 8.17/1.50  
% 8.17/1.50  fof(f11,axiom,(
% 8.17/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f26,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.17/1.50    inference(ennf_transformation,[],[f11])).
% 8.17/1.50  
% 8.17/1.50  fof(f84,plain,(
% 8.17/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.17/1.50    inference(cnf_transformation,[],[f26])).
% 8.17/1.50  
% 8.17/1.50  fof(f9,axiom,(
% 8.17/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f23,plain,(
% 8.17/1.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.17/1.50    inference(ennf_transformation,[],[f9])).
% 8.17/1.50  
% 8.17/1.50  fof(f24,plain,(
% 8.17/1.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.17/1.50    inference(flattening,[],[f23])).
% 8.17/1.50  
% 8.17/1.50  fof(f42,plain,(
% 8.17/1.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.17/1.50    inference(nnf_transformation,[],[f24])).
% 8.17/1.50  
% 8.17/1.50  fof(f43,plain,(
% 8.17/1.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.17/1.50    inference(rectify,[],[f42])).
% 8.17/1.50  
% 8.17/1.50  fof(f46,plain,(
% 8.17/1.50    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 8.17/1.50    introduced(choice_axiom,[])).
% 8.17/1.50  
% 8.17/1.50  fof(f45,plain,(
% 8.17/1.50    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 8.17/1.50    introduced(choice_axiom,[])).
% 8.17/1.50  
% 8.17/1.50  fof(f44,plain,(
% 8.17/1.50    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 8.17/1.50    introduced(choice_axiom,[])).
% 8.17/1.50  
% 8.17/1.50  fof(f47,plain,(
% 8.17/1.50    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.17/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f46,f45,f44])).
% 8.17/1.50  
% 8.17/1.50  fof(f79,plain,(
% 8.17/1.50    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.17/1.50    inference(cnf_transformation,[],[f47])).
% 8.17/1.50  
% 8.17/1.50  fof(f95,plain,(
% 8.17/1.50    v1_funct_1(sK8)),
% 8.17/1.50    inference(cnf_transformation,[],[f56])).
% 8.17/1.50  
% 8.17/1.50  fof(f12,axiom,(
% 8.17/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f27,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.17/1.50    inference(ennf_transformation,[],[f12])).
% 8.17/1.50  
% 8.17/1.50  fof(f85,plain,(
% 8.17/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.17/1.50    inference(cnf_transformation,[],[f27])).
% 8.17/1.50  
% 8.17/1.50  fof(f100,plain,(
% 8.17/1.50    k2_relset_1(sK6,sK7,sK8) != sK7),
% 8.17/1.50    inference(cnf_transformation,[],[f56])).
% 8.17/1.50  
% 8.17/1.50  fof(f13,axiom,(
% 8.17/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f28,plain,(
% 8.17/1.50    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.17/1.50    inference(ennf_transformation,[],[f13])).
% 8.17/1.50  
% 8.17/1.50  fof(f48,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.17/1.50    inference(nnf_transformation,[],[f28])).
% 8.17/1.50  
% 8.17/1.50  fof(f49,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.17/1.50    inference(rectify,[],[f48])).
% 8.17/1.50  
% 8.17/1.50  fof(f51,plain,(
% 8.17/1.50    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) & r2_hidden(sK5(X1,X2),X1)))),
% 8.17/1.50    introduced(choice_axiom,[])).
% 8.17/1.50  
% 8.17/1.50  fof(f50,plain,(
% 8.17/1.50    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) => r2_hidden(k4_tarski(sK4(X2,X3),X3),X2))),
% 8.17/1.50    introduced(choice_axiom,[])).
% 8.17/1.50  
% 8.17/1.50  fof(f52,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(sK4(X2,X3),X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) & r2_hidden(sK5(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.17/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f49,f51,f50])).
% 8.17/1.50  
% 8.17/1.50  fof(f86,plain,(
% 8.17/1.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK5(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.17/1.50    inference(cnf_transformation,[],[f52])).
% 8.17/1.50  
% 8.17/1.50  fof(f98,plain,(
% 8.17/1.50    ( ! [X3] : (r2_hidden(sK9(X3),sK6) | ~r2_hidden(X3,sK7)) )),
% 8.17/1.50    inference(cnf_transformation,[],[f56])).
% 8.17/1.50  
% 8.17/1.50  fof(f99,plain,(
% 8.17/1.50    ( ! [X3] : (k1_funct_1(sK8,sK9(X3)) = X3 | ~r2_hidden(X3,sK7)) )),
% 8.17/1.50    inference(cnf_transformation,[],[f56])).
% 8.17/1.50  
% 8.17/1.50  fof(f78,plain,(
% 8.17/1.50    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.17/1.50    inference(cnf_transformation,[],[f47])).
% 8.17/1.50  
% 8.17/1.50  fof(f105,plain,(
% 8.17/1.50    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.17/1.50    inference(equality_resolution,[],[f78])).
% 8.17/1.50  
% 8.17/1.50  fof(f106,plain,(
% 8.17/1.50    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.17/1.50    inference(equality_resolution,[],[f105])).
% 8.17/1.50  
% 8.17/1.50  fof(f6,axiom,(
% 8.17/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f20,plain,(
% 8.17/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 8.17/1.50    inference(ennf_transformation,[],[f6])).
% 8.17/1.50  
% 8.17/1.50  fof(f38,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.17/1.50    inference(nnf_transformation,[],[f20])).
% 8.17/1.50  
% 8.17/1.50  fof(f39,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.17/1.50    inference(rectify,[],[f38])).
% 8.17/1.50  
% 8.17/1.50  fof(f40,plain,(
% 8.17/1.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 8.17/1.50    introduced(choice_axiom,[])).
% 8.17/1.50  
% 8.17/1.50  fof(f41,plain,(
% 8.17/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 8.17/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 8.17/1.50  
% 8.17/1.50  fof(f67,plain,(
% 8.17/1.50    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 8.17/1.50    inference(cnf_transformation,[],[f41])).
% 8.17/1.50  
% 8.17/1.50  fof(f68,plain,(
% 8.17/1.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 8.17/1.50    inference(cnf_transformation,[],[f41])).
% 8.17/1.50  
% 8.17/1.50  fof(f70,plain,(
% 8.17/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 8.17/1.50    inference(cnf_transformation,[],[f41])).
% 8.17/1.50  
% 8.17/1.50  fof(f3,axiom,(
% 8.17/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f18,plain,(
% 8.17/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 8.17/1.50    inference(ennf_transformation,[],[f3])).
% 8.17/1.50  
% 8.17/1.50  fof(f63,plain,(
% 8.17/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 8.17/1.50    inference(cnf_transformation,[],[f18])).
% 8.17/1.50  
% 8.17/1.50  fof(f5,axiom,(
% 8.17/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f66,plain,(
% 8.17/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 8.17/1.50    inference(cnf_transformation,[],[f5])).
% 8.17/1.50  
% 8.17/1.50  fof(f87,plain,(
% 8.17/1.50    ( ! [X6,X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.17/1.50    inference(cnf_transformation,[],[f52])).
% 8.17/1.50  
% 8.17/1.50  fof(f90,plain,(
% 8.17/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.17/1.50    inference(cnf_transformation,[],[f53])).
% 8.17/1.50  
% 8.17/1.50  fof(f114,plain,(
% 8.17/1.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 8.17/1.50    inference(equality_resolution,[],[f90])).
% 8.17/1.50  
% 8.17/1.50  fof(f2,axiom,(
% 8.17/1.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f35,plain,(
% 8.17/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 8.17/1.50    inference(nnf_transformation,[],[f2])).
% 8.17/1.50  
% 8.17/1.50  fof(f36,plain,(
% 8.17/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 8.17/1.50    inference(flattening,[],[f35])).
% 8.17/1.50  
% 8.17/1.50  fof(f61,plain,(
% 8.17/1.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 8.17/1.50    inference(cnf_transformation,[],[f36])).
% 8.17/1.50  
% 8.17/1.50  fof(f104,plain,(
% 8.17/1.50    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 8.17/1.50    inference(equality_resolution,[],[f61])).
% 8.17/1.50  
% 8.17/1.50  fof(f62,plain,(
% 8.17/1.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 8.17/1.50    inference(cnf_transformation,[],[f36])).
% 8.17/1.50  
% 8.17/1.50  fof(f103,plain,(
% 8.17/1.50    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 8.17/1.50    inference(equality_resolution,[],[f62])).
% 8.17/1.50  
% 8.17/1.50  fof(f93,plain,(
% 8.17/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.17/1.50    inference(cnf_transformation,[],[f53])).
% 8.17/1.50  
% 8.17/1.50  fof(f112,plain,(
% 8.17/1.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 8.17/1.50    inference(equality_resolution,[],[f93])).
% 8.17/1.50  
% 8.17/1.50  fof(f7,axiom,(
% 8.17/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f72,plain,(
% 8.17/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 8.17/1.50    inference(cnf_transformation,[],[f7])).
% 8.17/1.50  
% 8.17/1.50  fof(f8,axiom,(
% 8.17/1.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 8.17/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.17/1.50  
% 8.17/1.50  fof(f21,plain,(
% 8.17/1.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 8.17/1.50    inference(ennf_transformation,[],[f8])).
% 8.17/1.50  
% 8.17/1.50  fof(f22,plain,(
% 8.17/1.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 8.17/1.50    inference(flattening,[],[f21])).
% 8.17/1.50  
% 8.17/1.50  fof(f73,plain,(
% 8.17/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.17/1.50    inference(cnf_transformation,[],[f22])).
% 8.17/1.50  
% 8.17/1.50  cnf(c_42,negated_conjecture,
% 8.17/1.50      ( v1_funct_2(sK8,sK6,sK7) ),
% 8.17/1.50      inference(cnf_transformation,[],[f96]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_37,plain,
% 8.17/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 8.17/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.17/1.50      | k1_relset_1(X1,X2,X0) = X1
% 8.17/1.50      | k1_xboole_0 = X2 ),
% 8.17/1.50      inference(cnf_transformation,[],[f89]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_41,negated_conjecture,
% 8.17/1.50      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 8.17/1.50      inference(cnf_transformation,[],[f97]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_483,plain,
% 8.17/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 8.17/1.50      | k1_relset_1(X1,X2,X0) = X1
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != X0
% 8.17/1.50      | k1_xboole_0 = X2 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_37,c_41]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_484,plain,
% 8.17/1.50      ( ~ v1_funct_2(sK8,X0,X1)
% 8.17/1.50      | k1_relset_1(X0,X1,sK8) = X0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | k1_xboole_0 = X1 ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_483]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_891,plain,
% 8.17/1.50      ( k1_relset_1(X0,X1,sK8) = X0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != sK8
% 8.17/1.50      | sK7 != X1
% 8.17/1.50      | sK6 != X0
% 8.17/1.50      | k1_xboole_0 = X1 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_42,c_484]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_892,plain,
% 8.17/1.50      ( k1_relset_1(sK6,sK7,sK8) = sK6
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | k1_xboole_0 = sK7 ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_891]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_969,plain,
% 8.17/1.50      ( k1_relset_1(sK6,sK7,sK8) = sK6 | k1_xboole_0 = sK7 ),
% 8.17/1.50      inference(equality_resolution_simp,[status(thm)],[c_892]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_27,plain,
% 8.17/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.17/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 8.17/1.50      inference(cnf_transformation,[],[f84]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_528,plain,
% 8.17/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != X2 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_27,c_41]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_529,plain,
% 8.17/1.50      ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_528]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12487,plain,
% 8.17/1.50      ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
% 8.17/1.50      inference(equality_resolution,[status(thm)],[c_529]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12529,plain,
% 8.17/1.50      ( k1_relat_1(sK8) = sK6 | sK7 = k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_969,c_12487]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_21,plain,
% 8.17/1.50      ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
% 8.17/1.50      | r2_hidden(sK1(X0,X1,X2),X2)
% 8.17/1.50      | ~ v1_funct_1(X0)
% 8.17/1.50      | ~ v1_relat_1(X0)
% 8.17/1.50      | k9_relat_1(X0,X1) = X2 ),
% 8.17/1.50      inference(cnf_transformation,[],[f79]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_43,negated_conjecture,
% 8.17/1.50      ( v1_funct_1(sK8) ),
% 8.17/1.50      inference(cnf_transformation,[],[f95]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_703,plain,
% 8.17/1.50      ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
% 8.17/1.50      | r2_hidden(sK1(X0,X1,X2),X2)
% 8.17/1.50      | ~ v1_relat_1(X0)
% 8.17/1.50      | k9_relat_1(X0,X1) = X2
% 8.17/1.50      | sK8 != X0 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_43]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_704,plain,
% 8.17/1.50      ( r2_hidden(sK2(sK8,X0,X1),k1_relat_1(sK8))
% 8.17/1.50      | r2_hidden(sK1(sK8,X0,X1),X1)
% 8.17/1.50      | ~ v1_relat_1(sK8)
% 8.17/1.50      | k9_relat_1(sK8,X0) = X1 ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_703]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12217,plain,
% 8.17/1.50      ( k9_relat_1(sK8,X0) = X1
% 8.17/1.50      | r2_hidden(sK2(sK8,X0,X1),k1_relat_1(sK8)) = iProver_top
% 8.17/1.50      | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
% 8.17/1.50      | v1_relat_1(sK8) != iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_13032,plain,
% 8.17/1.50      ( k9_relat_1(sK8,X0) = X1
% 8.17/1.50      | sK7 = k1_xboole_0
% 8.17/1.50      | r2_hidden(sK2(sK8,X0,X1),sK6) = iProver_top
% 8.17/1.50      | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
% 8.17/1.50      | v1_relat_1(sK8) != iProver_top ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_12529,c_12217]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28,plain,
% 8.17/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.17/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 8.17/1.50      inference(cnf_transformation,[],[f85]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_519,plain,
% 8.17/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != X2 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_28,c_41]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_520,plain,
% 8.17/1.50      ( k2_relset_1(X0,X1,sK8) = k2_relat_1(sK8)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_519]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12484,plain,
% 8.17/1.50      ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
% 8.17/1.50      inference(equality_resolution,[status(thm)],[c_520]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_38,negated_conjecture,
% 8.17/1.50      ( k2_relset_1(sK6,sK7,sK8) != sK7 ),
% 8.17/1.50      inference(cnf_transformation,[],[f100]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12492,plain,
% 8.17/1.50      ( k2_relat_1(sK8) != sK7 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_12484,c_38]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_31,plain,
% 8.17/1.50      ( r2_hidden(sK5(X0,X1),X0)
% 8.17/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
% 8.17/1.50      | k2_relset_1(X2,X0,X1) = X0 ),
% 8.17/1.50      inference(cnf_transformation,[],[f86]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_570,plain,
% 8.17/1.50      ( r2_hidden(sK5(X0,X1),X0)
% 8.17/1.50      | k2_relset_1(X2,X0,X1) = X0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != X1 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_31,c_41]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_571,plain,
% 8.17/1.50      ( r2_hidden(sK5(X0,sK8),X0)
% 8.17/1.50      | k2_relset_1(X1,X0,sK8) = X0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_570]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12218,plain,
% 8.17/1.50      ( k2_relset_1(X0,X1,sK8) = X1
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | r2_hidden(sK5(X1,sK8),X1) = iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12865,plain,
% 8.17/1.50      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 8.17/1.50      | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 8.17/1.50      inference(equality_resolution,[status(thm)],[c_12218]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12868,plain,
% 8.17/1.50      ( k2_relat_1(sK8) = sK7 | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_12865,c_12484]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_40,negated_conjecture,
% 8.17/1.50      ( ~ r2_hidden(X0,sK7) | r2_hidden(sK9(X0),sK6) ),
% 8.17/1.50      inference(cnf_transformation,[],[f98]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_13197,plain,
% 8.17/1.50      ( ~ r2_hidden(sK5(sK7,sK8),sK7) | r2_hidden(sK9(sK5(sK7,sK8)),sK6) ),
% 8.17/1.50      inference(instantiation,[status(thm)],[c_40]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_13201,plain,
% 8.17/1.50      ( r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
% 8.17/1.50      | r2_hidden(sK9(sK5(sK7,sK8)),sK6) = iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_13197]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_16129,plain,
% 8.17/1.50      ( r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 8.17/1.50      inference(global_propositional_subsumption,
% 8.17/1.50                [status(thm)],
% 8.17/1.50                [c_12868,c_12492]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_39,negated_conjecture,
% 8.17/1.50      ( ~ r2_hidden(X0,sK7) | k1_funct_1(sK8,sK9(X0)) = X0 ),
% 8.17/1.50      inference(cnf_transformation,[],[f99]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12227,plain,
% 8.17/1.50      ( k1_funct_1(sK8,sK9(X0)) = X0 | r2_hidden(X0,sK7) != iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_16134,plain,
% 8.17/1.50      ( k1_funct_1(sK8,sK9(sK5(sK7,sK8))) = sK5(sK7,sK8) ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_16129,c_12227]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12226,plain,
% 8.17/1.50      ( r2_hidden(X0,sK7) != iProver_top
% 8.17/1.50      | r2_hidden(sK9(X0),sK6) = iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_22,plain,
% 8.17/1.50      ( ~ r2_hidden(X0,X1)
% 8.17/1.50      | ~ r2_hidden(X0,k1_relat_1(X2))
% 8.17/1.50      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 8.17/1.50      | ~ v1_funct_1(X2)
% 8.17/1.50      | ~ v1_relat_1(X2) ),
% 8.17/1.50      inference(cnf_transformation,[],[f106]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_757,plain,
% 8.17/1.50      ( ~ r2_hidden(X0,X1)
% 8.17/1.50      | ~ r2_hidden(X0,k1_relat_1(X2))
% 8.17/1.50      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 8.17/1.50      | ~ v1_relat_1(X2)
% 8.17/1.50      | sK8 != X2 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_43]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_758,plain,
% 8.17/1.50      ( ~ r2_hidden(X0,X1)
% 8.17/1.50      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 8.17/1.50      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
% 8.17/1.50      | ~ v1_relat_1(sK8) ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_757]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12214,plain,
% 8.17/1.50      ( r2_hidden(X0,X1) != iProver_top
% 8.17/1.50      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 8.17/1.50      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
% 8.17/1.50      | v1_relat_1(sK8) != iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_13,plain,
% 8.17/1.50      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 8.17/1.50      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 8.17/1.50      | ~ v1_relat_1(X1) ),
% 8.17/1.50      inference(cnf_transformation,[],[f67]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12230,plain,
% 8.17/1.50      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 8.17/1.50      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 8.17/1.50      | v1_relat_1(X1) != iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12,plain,
% 8.17/1.50      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 8.17/1.50      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 8.17/1.50      | ~ v1_relat_1(X1) ),
% 8.17/1.50      inference(cnf_transformation,[],[f68]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12231,plain,
% 8.17/1.50      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 8.17/1.50      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 8.17/1.50      | v1_relat_1(X1) != iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_10,plain,
% 8.17/1.50      ( ~ r2_hidden(X0,X1)
% 8.17/1.50      | r2_hidden(X2,k9_relat_1(X3,X1))
% 8.17/1.50      | ~ r2_hidden(X0,k1_relat_1(X3))
% 8.17/1.50      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 8.17/1.50      | ~ v1_relat_1(X3) ),
% 8.17/1.50      inference(cnf_transformation,[],[f70]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12233,plain,
% 8.17/1.50      ( r2_hidden(X0,X1) != iProver_top
% 8.17/1.50      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 8.17/1.50      | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
% 8.17/1.50      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 8.17/1.50      | v1_relat_1(X3) != iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_13739,plain,
% 8.17/1.50      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 8.17/1.50      | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
% 8.17/1.50      | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
% 8.17/1.50      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) != iProver_top
% 8.17/1.50      | v1_relat_1(X1) != iProver_top ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_12231,c_12233]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_119,plain,
% 8.17/1.50      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 8.17/1.50      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 8.17/1.50      | v1_relat_1(X1) != iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_17558,plain,
% 8.17/1.50      ( r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
% 8.17/1.50      | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
% 8.17/1.50      | r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 8.17/1.50      | v1_relat_1(X1) != iProver_top ),
% 8.17/1.50      inference(global_propositional_subsumption,[status(thm)],[c_13739,c_119]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_17559,plain,
% 8.17/1.50      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 8.17/1.50      | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
% 8.17/1.50      | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
% 8.17/1.50      | v1_relat_1(X1) != iProver_top ),
% 8.17/1.50      inference(renaming,[status(thm)],[c_17558]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_17567,plain,
% 8.17/1.50      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 8.17/1.50      | r2_hidden(X0,k9_relat_1(X1,k1_relat_1(X1))) = iProver_top
% 8.17/1.50      | v1_relat_1(X1) != iProver_top ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_12230,c_17559]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_17611,plain,
% 8.17/1.50      ( r2_hidden(X0,X1) != iProver_top
% 8.17/1.50      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 8.17/1.50      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 8.17/1.50      | v1_relat_1(sK8) != iProver_top ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_12214,c_17567]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_6,plain,
% 8.17/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 8.17/1.50      inference(cnf_transformation,[],[f63]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_453,plain,
% 8.17/1.50      ( ~ v1_relat_1(X0)
% 8.17/1.50      | v1_relat_1(X1)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0)
% 8.17/1.50      | sK8 != X1 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_6,c_41]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_454,plain,
% 8.17/1.50      ( ~ v1_relat_1(X0)
% 8.17/1.50      | v1_relat_1(sK8)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0) ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_453]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12222,plain,
% 8.17/1.50      ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0)
% 8.17/1.50      | v1_relat_1(X0) != iProver_top
% 8.17/1.50      | v1_relat_1(sK8) = iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12603,plain,
% 8.17/1.50      ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) != iProver_top
% 8.17/1.50      | v1_relat_1(sK8) = iProver_top ),
% 8.17/1.50      inference(equality_resolution,[status(thm)],[c_12222]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_9,plain,
% 8.17/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 8.17/1.50      inference(cnf_transformation,[],[f66]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12234,plain,
% 8.17/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_13216,plain,
% 8.17/1.50      ( v1_relat_1(sK8) = iProver_top ),
% 8.17/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_12603,c_12234]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_17916,plain,
% 8.17/1.50      ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 8.17/1.50      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 8.17/1.50      | r2_hidden(X0,X1) != iProver_top ),
% 8.17/1.50      inference(global_propositional_subsumption,
% 8.17/1.50                [status(thm)],
% 8.17/1.50                [c_17611,c_13216]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_17917,plain,
% 8.17/1.50      ( r2_hidden(X0,X1) != iProver_top
% 8.17/1.50      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 8.17/1.50      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top ),
% 8.17/1.50      inference(renaming,[status(thm)],[c_17916]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_17928,plain,
% 8.17/1.50      ( r2_hidden(X0,sK7) != iProver_top
% 8.17/1.50      | r2_hidden(k1_funct_1(sK8,sK9(X0)),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 8.17/1.50      | r2_hidden(sK9(X0),k1_relat_1(sK8)) != iProver_top ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_12226,c_17917]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_18137,plain,
% 8.17/1.50      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 8.17/1.50      | r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
% 8.17/1.50      | r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_16134,c_17928]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_18229,plain,
% 8.17/1.50      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 8.17/1.50      | r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
% 8.17/1.50      inference(global_propositional_subsumption,
% 8.17/1.50                [status(thm)],
% 8.17/1.50                [c_18137,c_12492,c_12868]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_30,plain,
% 8.17/1.50      ( ~ r2_hidden(k4_tarski(X0,sK5(X1,X2)),X2)
% 8.17/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 8.17/1.50      | k2_relset_1(X3,X1,X2) = X1 ),
% 8.17/1.50      inference(cnf_transformation,[],[f87]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_537,plain,
% 8.17/1.50      ( ~ r2_hidden(k4_tarski(X0,sK5(X1,X2)),X2)
% 8.17/1.50      | k2_relset_1(X3,X1,X2) = X1
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != X2 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_538,plain,
% 8.17/1.50      ( ~ r2_hidden(k4_tarski(X0,sK5(X1,sK8)),sK8)
% 8.17/1.50      | k2_relset_1(X2,X1,sK8) = X1
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_537]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12220,plain,
% 8.17/1.50      ( k2_relset_1(X0,X1,sK8) = X1
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | r2_hidden(k4_tarski(X2,sK5(X1,sK8)),sK8) != iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12731,plain,
% 8.17/1.50      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 8.17/1.50      | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 8.17/1.50      inference(equality_resolution,[status(thm)],[c_12220]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12734,plain,
% 8.17/1.50      ( k2_relat_1(sK8) = sK7
% 8.17/1.50      | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_12731,c_12484]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_13452,plain,
% 8.17/1.50      ( r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 8.17/1.50      inference(global_propositional_subsumption,
% 8.17/1.50                [status(thm)],
% 8.17/1.50                [c_12734,c_12492]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_13657,plain,
% 8.17/1.50      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top
% 8.17/1.50      | v1_relat_1(sK8) != iProver_top ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_12231,c_13452]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_14829,plain,
% 8.17/1.50      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top ),
% 8.17/1.50      inference(global_propositional_subsumption,
% 8.17/1.50                [status(thm)],
% 8.17/1.50                [c_13657,c_13216]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_18235,plain,
% 8.17/1.50      ( r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
% 8.17/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_18229,c_14829]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_18237,plain,
% 8.17/1.50      ( sK7 = k1_xboole_0 | r2_hidden(sK9(sK5(sK7,sK8)),sK6) != iProver_top ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_12529,c_18235]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28851,plain,
% 8.17/1.50      ( sK7 = k1_xboole_0 ),
% 8.17/1.50      inference(global_propositional_subsumption,
% 8.17/1.50                [status(thm)],
% 8.17/1.50                [c_13032,c_12492,c_12868,c_13201,c_18237]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_36,plain,
% 8.17/1.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 8.17/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 8.17/1.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 8.17/1.50      inference(cnf_transformation,[],[f114]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_620,plain,
% 8.17/1.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 8.17/1.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != X0 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_36,c_41]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_621,plain,
% 8.17/1.50      ( ~ v1_funct_2(sK8,k1_xboole_0,X0)
% 8.17/1.50      | k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_620]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_916,plain,
% 8.17/1.50      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != sK8
% 8.17/1.50      | sK7 != X0
% 8.17/1.50      | sK6 != k1_xboole_0 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_42,c_621]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_917,plain,
% 8.17/1.50      ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK6 != k1_xboole_0 ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_916]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_4,plain,
% 8.17/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 8.17/1.50      inference(cnf_transformation,[],[f104]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12316,plain,
% 8.17/1.50      ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k1_xboole_0)
% 8.17/1.50      | sK6 != k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_917,c_4]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28919,plain,
% 8.17/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 8.17/1.50      | sK6 != k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_28851,c_12316]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12581,plain,
% 8.17/1.50      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k1_xboole_0) ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_4,c_529]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28922,plain,
% 8.17/1.50      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_28851,c_12581]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_3,plain,
% 8.17/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 8.17/1.50      inference(cnf_transformation,[],[f103]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28968,plain,
% 8.17/1.50      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 8.17/1.50      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_28922,c_3]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28969,plain,
% 8.17/1.50      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8) ),
% 8.17/1.50      inference(equality_resolution_simp,[status(thm)],[c_28968]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28976,plain,
% 8.17/1.50      ( k1_relat_1(sK8) = k1_xboole_0
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 8.17/1.50      | sK6 != k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_28919,c_28969]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28980,plain,
% 8.17/1.50      ( k1_relat_1(sK8) = k1_xboole_0
% 8.17/1.50      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 8.17/1.50      | sK6 != k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_28976,c_3]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28981,plain,
% 8.17/1.50      ( k1_relat_1(sK8) = k1_xboole_0 | sK6 != k1_xboole_0 ),
% 8.17/1.50      inference(equality_resolution_simp,[status(thm)],[c_28980]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_33,plain,
% 8.17/1.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 8.17/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 8.17/1.50      | k1_xboole_0 = X1
% 8.17/1.50      | k1_xboole_0 = X0 ),
% 8.17/1.50      inference(cnf_transformation,[],[f112]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_602,plain,
% 8.17/1.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != X0
% 8.17/1.50      | k1_xboole_0 = X1
% 8.17/1.50      | k1_xboole_0 = X0 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_33,c_41]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_603,plain,
% 8.17/1.50      ( ~ v1_funct_2(sK8,X0,k1_xboole_0)
% 8.17/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | k1_xboole_0 = X0
% 8.17/1.50      | k1_xboole_0 = sK8 ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_602]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_902,plain,
% 8.17/1.50      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 != sK8
% 8.17/1.50      | sK8 = k1_xboole_0
% 8.17/1.50      | sK7 != k1_xboole_0
% 8.17/1.50      | sK6 != X0
% 8.17/1.50      | k1_xboole_0 = X0 ),
% 8.17/1.50      inference(resolution_lifted,[status(thm)],[c_42,c_603]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_903,plain,
% 8.17/1.50      ( k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 8.17/1.50      | sK8 = k1_xboole_0
% 8.17/1.50      | sK7 != k1_xboole_0
% 8.17/1.50      | k1_xboole_0 = sK6 ),
% 8.17/1.50      inference(unflattening,[status(thm)],[c_902]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12324,plain,
% 8.17/1.50      ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k1_xboole_0)
% 8.17/1.50      | sK8 = k1_xboole_0
% 8.17/1.50      | sK7 != k1_xboole_0
% 8.17/1.50      | sK6 = k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_903,c_3]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28914,plain,
% 8.17/1.50      ( k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 8.17/1.50      | sK8 = k1_xboole_0
% 8.17/1.50      | sK6 = k1_xboole_0
% 8.17/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_28851,c_12324]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_29013,plain,
% 8.17/1.50      ( k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 8.17/1.50      | sK8 = k1_xboole_0
% 8.17/1.50      | sK6 = k1_xboole_0 ),
% 8.17/1.50      inference(equality_resolution_simp,[status(thm)],[c_28914]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_29017,plain,
% 8.17/1.50      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 8.17/1.50      | sK8 = k1_xboole_0
% 8.17/1.50      | sK6 = k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_29013,c_3]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_29018,plain,
% 8.17/1.50      ( sK8 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 8.17/1.50      inference(equality_resolution_simp,[status(thm)],[c_29017]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_28926,plain,
% 8.17/1.50      ( k2_relat_1(sK8) != k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_28851,c_12492]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_33453,plain,
% 8.17/1.50      ( k2_relat_1(k1_xboole_0) != k1_xboole_0 | sK6 = k1_xboole_0 ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_29018,c_28926]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_14,plain,
% 8.17/1.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 8.17/1.50      inference(cnf_transformation,[],[f72]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_34096,plain,
% 8.17/1.50      ( sK6 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 8.17/1.50      inference(light_normalisation,[status(thm)],[c_33453,c_14]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_34097,plain,
% 8.17/1.50      ( sK6 = k1_xboole_0 ),
% 8.17/1.50      inference(equality_resolution_simp,[status(thm)],[c_34096]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_34814,plain,
% 8.17/1.50      ( k1_relat_1(sK8) = k1_xboole_0 ),
% 8.17/1.50      inference(global_propositional_subsumption,
% 8.17/1.50                [status(thm)],
% 8.17/1.50                [c_28981,c_34097]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_17,plain,
% 8.17/1.50      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 8.17/1.50      inference(cnf_transformation,[],[f73]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_12228,plain,
% 8.17/1.50      ( k1_relat_1(X0) != k1_xboole_0
% 8.17/1.50      | k1_xboole_0 = X0
% 8.17/1.50      | v1_relat_1(X0) != iProver_top ),
% 8.17/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_35328,plain,
% 8.17/1.50      ( sK8 = k1_xboole_0 | v1_relat_1(sK8) != iProver_top ),
% 8.17/1.50      inference(superposition,[status(thm)],[c_34814,c_12228]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_35380,plain,
% 8.17/1.50      ( sK8 = k1_xboole_0 ),
% 8.17/1.50      inference(global_propositional_subsumption,
% 8.17/1.50                [status(thm)],
% 8.17/1.50                [c_35328,c_13216]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_35402,plain,
% 8.17/1.50      ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 8.17/1.50      inference(demodulation,[status(thm)],[c_35380,c_28926]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_35579,plain,
% 8.17/1.50      ( k1_xboole_0 != k1_xboole_0 ),
% 8.17/1.50      inference(light_normalisation,[status(thm)],[c_35402,c_14]) ).
% 8.17/1.50  
% 8.17/1.50  cnf(c_35580,plain,
% 8.17/1.50      ( $false ),
% 8.17/1.50      inference(equality_resolution_simp,[status(thm)],[c_35579]) ).
% 8.17/1.50  
% 8.17/1.50  
% 8.17/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.17/1.50  
% 8.17/1.50  ------                               Statistics
% 8.17/1.50  
% 8.17/1.50  ------ Selected
% 8.17/1.50  
% 8.17/1.50  total_time:                             0.941
% 8.17/1.50  
%------------------------------------------------------------------------------

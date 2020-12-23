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
% DateTime   : Thu Dec  3 12:04:13 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 259 expanded)
%              Number of clauses        :   57 (  77 expanded)
%              Number of leaves         :   17 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  488 (1586 expanded)
%              Number of equality atoms :  188 ( 469 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X4,X2,X0,X3] :
      ( ? [X5] :
          ( k1_funct_1(X3,X5) = X4
          & r2_hidden(X5,X2)
          & r2_hidden(X5,X0) )
     => ( k1_funct_1(X3,sK10) = X4
        & r2_hidden(sK10,X2)
        & r2_hidden(sK10,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
     => ( ~ r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2))
        & ? [X5] :
            ( k1_funct_1(X3,X5) = sK9
            & r2_hidden(X5,X2)
            & r2_hidden(X5,X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
            & ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) ) )
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))
          & ? [X5] :
              ( k1_funct_1(sK8,X5) = X4
              & r2_hidden(X5,sK7)
              & r2_hidden(X5,sK5) ) )
      & k1_xboole_0 != sK6
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & k1_funct_1(sK8,sK10) = sK9
    & r2_hidden(sK10,sK7)
    & r2_hidden(sK10,sK5)
    & k1_xboole_0 != sK6
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f20,f37,f36,f35])).

fof(f68,plain,(
    k1_funct_1(sK8,sK10) = sK9 ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).

fof(f44,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f71,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f62,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    r2_hidden(sK10,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f32,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK4(X1,X2),X6),X2)
        & r2_hidden(sK4(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK4(X1,X2),X6),X2)
            & r2_hidden(sK4(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f32,f31])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    r2_hidden(sK10,sK7) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_24,negated_conjecture,
    ( k1_funct_1(sK8,sK10) = sK9 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_632,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_633,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_1303,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_634,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_973,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1517,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_322,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_323,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_1512,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1597,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_1598,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1653,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1654,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1653])).

cnf(c_2403,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1303,c_634,c_1517,c_1598,c_1654])).

cnf(c_2404,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2403])).

cnf(c_2412,plain,
    ( r2_hidden(sK10,X0) != iProver_top
    | r2_hidden(sK10,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_2404])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK10,sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34,plain,
    ( r2_hidden(sK10,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_337,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_338,plain,
    ( ~ v1_funct_2(sK8,X0,X1)
    | k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_787,plain,
    ( k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != sK8
    | sK6 != X1
    | sK5 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_338])).

cnf(c_788,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_789,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | k1_relset_1(sK5,sK6,sK8) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_788,c_27])).

cnf(c_790,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(renaming,[status(thm)],[c_789])).

cnf(c_858,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_790])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK3(X2,X0)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | k1_relset_1(X1,X3,X2) != X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK3(X2,X0)),X2)
    | k1_relset_1(X1,X3,X2) != X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_383,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK3(sK8,X0)),sK8)
    | k1_relset_1(X1,X2,sK8) != X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_1507,plain,
    ( r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8)
    | ~ r2_hidden(sK10,sK5)
    | k1_relset_1(sK5,X0,sK8) != sK5
    | k1_zfmisc_1(k2_zfmisc_1(sK5,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_1631,plain,
    ( r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8)
    | ~ r2_hidden(sK10,sK5)
    | k1_relset_1(sK5,sK6,sK8) != sK5
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_1632,plain,
    ( k1_relset_1(sK5,sK6,sK8) != sK5
    | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8) = iProver_top
    | r2_hidden(sK10,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1631])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_542,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_543,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_1751,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8)
    | r2_hidden(sK10,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1752,plain,
    ( r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8) != iProver_top
    | r2_hidden(sK10,k1_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1751])).

cnf(c_2433,plain,
    ( r2_hidden(sK10,X0) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2412,c_34,c_858,c_1517,c_1598,c_1632,c_1654,c_1752])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_373,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_374,plain,
    ( k7_relset_1(X0,X1,sK8,X2) = k9_relat_1(sK8,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_1538,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(equality_resolution,[status(thm)],[c_374])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1316,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1625,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1538,c_1316])).

cnf(c_2442,plain,
    ( r2_hidden(sK10,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2433,c_1625])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK10,sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( r2_hidden(sK10,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2442,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 1.96/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.02  
% 1.96/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.96/1.02  
% 1.96/1.02  ------  iProver source info
% 1.96/1.02  
% 1.96/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.96/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.96/1.02  git: non_committed_changes: false
% 1.96/1.02  git: last_make_outside_of_git: false
% 1.96/1.02  
% 1.96/1.02  ------ 
% 1.96/1.02  
% 1.96/1.02  ------ Input Options
% 1.96/1.02  
% 1.96/1.02  --out_options                           all
% 1.96/1.02  --tptp_safe_out                         true
% 1.96/1.02  --problem_path                          ""
% 1.96/1.02  --include_path                          ""
% 1.96/1.02  --clausifier                            res/vclausify_rel
% 1.96/1.02  --clausifier_options                    --mode clausify
% 1.96/1.02  --stdin                                 false
% 1.96/1.02  --stats_out                             all
% 1.96/1.02  
% 1.96/1.02  ------ General Options
% 1.96/1.02  
% 1.96/1.02  --fof                                   false
% 1.96/1.02  --time_out_real                         305.
% 1.96/1.02  --time_out_virtual                      -1.
% 1.96/1.02  --symbol_type_check                     false
% 1.96/1.02  --clausify_out                          false
% 1.96/1.02  --sig_cnt_out                           false
% 1.96/1.02  --trig_cnt_out                          false
% 1.96/1.02  --trig_cnt_out_tolerance                1.
% 1.96/1.02  --trig_cnt_out_sk_spl                   false
% 1.96/1.02  --abstr_cl_out                          false
% 1.96/1.02  
% 1.96/1.02  ------ Global Options
% 1.96/1.02  
% 1.96/1.02  --schedule                              default
% 1.96/1.02  --add_important_lit                     false
% 1.96/1.02  --prop_solver_per_cl                    1000
% 1.96/1.02  --min_unsat_core                        false
% 1.96/1.02  --soft_assumptions                      false
% 1.96/1.02  --soft_lemma_size                       3
% 1.96/1.02  --prop_impl_unit_size                   0
% 1.96/1.02  --prop_impl_unit                        []
% 1.96/1.02  --share_sel_clauses                     true
% 1.96/1.02  --reset_solvers                         false
% 1.96/1.02  --bc_imp_inh                            [conj_cone]
% 1.96/1.02  --conj_cone_tolerance                   3.
% 1.96/1.02  --extra_neg_conj                        none
% 1.96/1.02  --large_theory_mode                     true
% 1.96/1.02  --prolific_symb_bound                   200
% 1.96/1.02  --lt_threshold                          2000
% 1.96/1.02  --clause_weak_htbl                      true
% 1.96/1.02  --gc_record_bc_elim                     false
% 1.96/1.02  
% 1.96/1.02  ------ Preprocessing Options
% 1.96/1.02  
% 1.96/1.02  --preprocessing_flag                    true
% 1.96/1.02  --time_out_prep_mult                    0.1
% 1.96/1.02  --splitting_mode                        input
% 1.96/1.02  --splitting_grd                         true
% 1.96/1.02  --splitting_cvd                         false
% 1.96/1.02  --splitting_cvd_svl                     false
% 1.96/1.02  --splitting_nvd                         32
% 1.96/1.02  --sub_typing                            true
% 1.96/1.02  --prep_gs_sim                           true
% 1.96/1.02  --prep_unflatten                        true
% 1.96/1.02  --prep_res_sim                          true
% 1.96/1.02  --prep_upred                            true
% 1.96/1.02  --prep_sem_filter                       exhaustive
% 1.96/1.02  --prep_sem_filter_out                   false
% 1.96/1.02  --pred_elim                             true
% 1.96/1.02  --res_sim_input                         true
% 1.96/1.02  --eq_ax_congr_red                       true
% 1.96/1.02  --pure_diseq_elim                       true
% 1.96/1.02  --brand_transform                       false
% 1.96/1.02  --non_eq_to_eq                          false
% 1.96/1.02  --prep_def_merge                        true
% 1.96/1.02  --prep_def_merge_prop_impl              false
% 1.96/1.02  --prep_def_merge_mbd                    true
% 1.96/1.02  --prep_def_merge_tr_red                 false
% 1.96/1.02  --prep_def_merge_tr_cl                  false
% 1.96/1.02  --smt_preprocessing                     true
% 1.96/1.02  --smt_ac_axioms                         fast
% 1.96/1.02  --preprocessed_out                      false
% 1.96/1.02  --preprocessed_stats                    false
% 1.96/1.02  
% 1.96/1.02  ------ Abstraction refinement Options
% 1.96/1.02  
% 1.96/1.02  --abstr_ref                             []
% 1.96/1.02  --abstr_ref_prep                        false
% 1.96/1.02  --abstr_ref_until_sat                   false
% 1.96/1.02  --abstr_ref_sig_restrict                funpre
% 1.96/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.02  --abstr_ref_under                       []
% 1.96/1.02  
% 1.96/1.02  ------ SAT Options
% 1.96/1.02  
% 1.96/1.02  --sat_mode                              false
% 1.96/1.02  --sat_fm_restart_options                ""
% 1.96/1.02  --sat_gr_def                            false
% 1.96/1.02  --sat_epr_types                         true
% 1.96/1.02  --sat_non_cyclic_types                  false
% 1.96/1.02  --sat_finite_models                     false
% 1.96/1.02  --sat_fm_lemmas                         false
% 1.96/1.02  --sat_fm_prep                           false
% 1.96/1.02  --sat_fm_uc_incr                        true
% 1.96/1.02  --sat_out_model                         small
% 1.96/1.02  --sat_out_clauses                       false
% 1.96/1.02  
% 1.96/1.02  ------ QBF Options
% 1.96/1.02  
% 1.96/1.02  --qbf_mode                              false
% 1.96/1.02  --qbf_elim_univ                         false
% 1.96/1.02  --qbf_dom_inst                          none
% 1.96/1.02  --qbf_dom_pre_inst                      false
% 1.96/1.02  --qbf_sk_in                             false
% 1.96/1.02  --qbf_pred_elim                         true
% 1.96/1.02  --qbf_split                             512
% 1.96/1.02  
% 1.96/1.02  ------ BMC1 Options
% 1.96/1.02  
% 1.96/1.02  --bmc1_incremental                      false
% 1.96/1.02  --bmc1_axioms                           reachable_all
% 1.96/1.02  --bmc1_min_bound                        0
% 1.96/1.02  --bmc1_max_bound                        -1
% 1.96/1.02  --bmc1_max_bound_default                -1
% 1.96/1.02  --bmc1_symbol_reachability              true
% 1.96/1.02  --bmc1_property_lemmas                  false
% 1.96/1.02  --bmc1_k_induction                      false
% 1.96/1.02  --bmc1_non_equiv_states                 false
% 1.96/1.02  --bmc1_deadlock                         false
% 1.96/1.02  --bmc1_ucm                              false
% 1.96/1.02  --bmc1_add_unsat_core                   none
% 1.96/1.02  --bmc1_unsat_core_children              false
% 1.96/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.02  --bmc1_out_stat                         full
% 1.96/1.02  --bmc1_ground_init                      false
% 1.96/1.02  --bmc1_pre_inst_next_state              false
% 1.96/1.02  --bmc1_pre_inst_state                   false
% 1.96/1.02  --bmc1_pre_inst_reach_state             false
% 1.96/1.02  --bmc1_out_unsat_core                   false
% 1.96/1.02  --bmc1_aig_witness_out                  false
% 1.96/1.02  --bmc1_verbose                          false
% 1.96/1.02  --bmc1_dump_clauses_tptp                false
% 1.96/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.02  --bmc1_dump_file                        -
% 1.96/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.02  --bmc1_ucm_extend_mode                  1
% 1.96/1.02  --bmc1_ucm_init_mode                    2
% 1.96/1.02  --bmc1_ucm_cone_mode                    none
% 1.96/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.02  --bmc1_ucm_relax_model                  4
% 1.96/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.02  --bmc1_ucm_layered_model                none
% 1.96/1.02  --bmc1_ucm_max_lemma_size               10
% 1.96/1.02  
% 1.96/1.02  ------ AIG Options
% 1.96/1.02  
% 1.96/1.02  --aig_mode                              false
% 1.96/1.02  
% 1.96/1.02  ------ Instantiation Options
% 1.96/1.02  
% 1.96/1.02  --instantiation_flag                    true
% 1.96/1.02  --inst_sos_flag                         false
% 1.96/1.02  --inst_sos_phase                        true
% 1.96/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.02  --inst_lit_sel_side                     num_symb
% 1.96/1.02  --inst_solver_per_active                1400
% 1.96/1.02  --inst_solver_calls_frac                1.
% 1.96/1.02  --inst_passive_queue_type               priority_queues
% 1.96/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.02  --inst_passive_queues_freq              [25;2]
% 1.96/1.02  --inst_dismatching                      true
% 1.96/1.02  --inst_eager_unprocessed_to_passive     true
% 1.96/1.02  --inst_prop_sim_given                   true
% 1.96/1.02  --inst_prop_sim_new                     false
% 1.96/1.02  --inst_subs_new                         false
% 1.96/1.02  --inst_eq_res_simp                      false
% 1.96/1.02  --inst_subs_given                       false
% 1.96/1.02  --inst_orphan_elimination               true
% 1.96/1.02  --inst_learning_loop_flag               true
% 1.96/1.02  --inst_learning_start                   3000
% 1.96/1.02  --inst_learning_factor                  2
% 1.96/1.02  --inst_start_prop_sim_after_learn       3
% 1.96/1.02  --inst_sel_renew                        solver
% 1.96/1.02  --inst_lit_activity_flag                true
% 1.96/1.02  --inst_restr_to_given                   false
% 1.96/1.02  --inst_activity_threshold               500
% 1.96/1.02  --inst_out_proof                        true
% 1.96/1.02  
% 1.96/1.02  ------ Resolution Options
% 1.96/1.02  
% 1.96/1.02  --resolution_flag                       true
% 1.96/1.02  --res_lit_sel                           adaptive
% 1.96/1.02  --res_lit_sel_side                      none
% 1.96/1.02  --res_ordering                          kbo
% 1.96/1.02  --res_to_prop_solver                    active
% 1.96/1.02  --res_prop_simpl_new                    false
% 1.96/1.02  --res_prop_simpl_given                  true
% 1.96/1.02  --res_passive_queue_type                priority_queues
% 1.96/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.02  --res_passive_queues_freq               [15;5]
% 1.96/1.02  --res_forward_subs                      full
% 1.96/1.02  --res_backward_subs                     full
% 1.96/1.02  --res_forward_subs_resolution           true
% 1.96/1.02  --res_backward_subs_resolution          true
% 1.96/1.02  --res_orphan_elimination                true
% 1.96/1.02  --res_time_limit                        2.
% 1.96/1.02  --res_out_proof                         true
% 1.96/1.02  
% 1.96/1.02  ------ Superposition Options
% 1.96/1.02  
% 1.96/1.02  --superposition_flag                    true
% 1.96/1.02  --sup_passive_queue_type                priority_queues
% 1.96/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.02  --demod_completeness_check              fast
% 1.96/1.02  --demod_use_ground                      true
% 1.96/1.02  --sup_to_prop_solver                    passive
% 1.96/1.02  --sup_prop_simpl_new                    true
% 1.96/1.02  --sup_prop_simpl_given                  true
% 1.96/1.02  --sup_fun_splitting                     false
% 1.96/1.02  --sup_smt_interval                      50000
% 1.96/1.02  
% 1.96/1.02  ------ Superposition Simplification Setup
% 1.96/1.02  
% 1.96/1.02  --sup_indices_passive                   []
% 1.96/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.02  --sup_full_bw                           [BwDemod]
% 1.96/1.02  --sup_immed_triv                        [TrivRules]
% 1.96/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.02  --sup_immed_bw_main                     []
% 1.96/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.02  
% 1.96/1.02  ------ Combination Options
% 1.96/1.02  
% 1.96/1.02  --comb_res_mult                         3
% 1.96/1.02  --comb_sup_mult                         2
% 1.96/1.02  --comb_inst_mult                        10
% 1.96/1.02  
% 1.96/1.02  ------ Debug Options
% 1.96/1.02  
% 1.96/1.02  --dbg_backtrace                         false
% 1.96/1.02  --dbg_dump_prop_clauses                 false
% 1.96/1.02  --dbg_dump_prop_clauses_file            -
% 1.96/1.02  --dbg_out_stat                          false
% 1.96/1.02  ------ Parsing...
% 1.96/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.96/1.02  
% 1.96/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.96/1.02  
% 1.96/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.96/1.02  
% 1.96/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.96/1.02  ------ Proving...
% 1.96/1.02  ------ Problem Properties 
% 1.96/1.02  
% 1.96/1.02  
% 1.96/1.02  clauses                                 25
% 1.96/1.02  conjectures                             5
% 1.96/1.02  EPR                                     3
% 1.96/1.02  Horn                                    20
% 1.96/1.02  unary                                   7
% 1.96/1.02  binary                                  1
% 1.96/1.02  lits                                    69
% 1.96/1.02  lits eq                                 27
% 1.96/1.02  fd_pure                                 0
% 1.96/1.02  fd_pseudo                               0
% 1.96/1.02  fd_cond                                 0
% 1.96/1.02  fd_pseudo_cond                          5
% 1.96/1.02  AC symbols                              0
% 1.96/1.02  
% 1.96/1.02  ------ Schedule dynamic 5 is on 
% 1.96/1.02  
% 1.96/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.96/1.02  
% 1.96/1.02  
% 1.96/1.02  ------ 
% 1.96/1.02  Current options:
% 1.96/1.02  ------ 
% 1.96/1.02  
% 1.96/1.02  ------ Input Options
% 1.96/1.02  
% 1.96/1.02  --out_options                           all
% 1.96/1.02  --tptp_safe_out                         true
% 1.96/1.02  --problem_path                          ""
% 1.96/1.02  --include_path                          ""
% 1.96/1.02  --clausifier                            res/vclausify_rel
% 1.96/1.02  --clausifier_options                    --mode clausify
% 1.96/1.02  --stdin                                 false
% 1.96/1.02  --stats_out                             all
% 1.96/1.02  
% 1.96/1.02  ------ General Options
% 1.96/1.02  
% 1.96/1.02  --fof                                   false
% 1.96/1.02  --time_out_real                         305.
% 1.96/1.02  --time_out_virtual                      -1.
% 1.96/1.02  --symbol_type_check                     false
% 1.96/1.02  --clausify_out                          false
% 1.96/1.02  --sig_cnt_out                           false
% 1.96/1.02  --trig_cnt_out                          false
% 1.96/1.02  --trig_cnt_out_tolerance                1.
% 1.96/1.02  --trig_cnt_out_sk_spl                   false
% 1.96/1.02  --abstr_cl_out                          false
% 1.96/1.02  
% 1.96/1.02  ------ Global Options
% 1.96/1.02  
% 1.96/1.02  --schedule                              default
% 1.96/1.02  --add_important_lit                     false
% 1.96/1.02  --prop_solver_per_cl                    1000
% 1.96/1.02  --min_unsat_core                        false
% 1.96/1.02  --soft_assumptions                      false
% 1.96/1.02  --soft_lemma_size                       3
% 1.96/1.02  --prop_impl_unit_size                   0
% 1.96/1.02  --prop_impl_unit                        []
% 1.96/1.02  --share_sel_clauses                     true
% 1.96/1.02  --reset_solvers                         false
% 1.96/1.02  --bc_imp_inh                            [conj_cone]
% 1.96/1.02  --conj_cone_tolerance                   3.
% 1.96/1.02  --extra_neg_conj                        none
% 1.96/1.02  --large_theory_mode                     true
% 1.96/1.02  --prolific_symb_bound                   200
% 1.96/1.02  --lt_threshold                          2000
% 1.96/1.02  --clause_weak_htbl                      true
% 1.96/1.02  --gc_record_bc_elim                     false
% 1.96/1.02  
% 1.96/1.02  ------ Preprocessing Options
% 1.96/1.02  
% 1.96/1.02  --preprocessing_flag                    true
% 1.96/1.02  --time_out_prep_mult                    0.1
% 1.96/1.02  --splitting_mode                        input
% 1.96/1.02  --splitting_grd                         true
% 1.96/1.02  --splitting_cvd                         false
% 1.96/1.02  --splitting_cvd_svl                     false
% 1.96/1.02  --splitting_nvd                         32
% 1.96/1.02  --sub_typing                            true
% 1.96/1.02  --prep_gs_sim                           true
% 1.96/1.02  --prep_unflatten                        true
% 1.96/1.02  --prep_res_sim                          true
% 1.96/1.02  --prep_upred                            true
% 1.96/1.02  --prep_sem_filter                       exhaustive
% 1.96/1.02  --prep_sem_filter_out                   false
% 1.96/1.02  --pred_elim                             true
% 1.96/1.02  --res_sim_input                         true
% 1.96/1.02  --eq_ax_congr_red                       true
% 1.96/1.02  --pure_diseq_elim                       true
% 1.96/1.02  --brand_transform                       false
% 1.96/1.02  --non_eq_to_eq                          false
% 1.96/1.02  --prep_def_merge                        true
% 1.96/1.02  --prep_def_merge_prop_impl              false
% 1.96/1.02  --prep_def_merge_mbd                    true
% 1.96/1.02  --prep_def_merge_tr_red                 false
% 1.96/1.02  --prep_def_merge_tr_cl                  false
% 1.96/1.02  --smt_preprocessing                     true
% 1.96/1.02  --smt_ac_axioms                         fast
% 1.96/1.02  --preprocessed_out                      false
% 1.96/1.02  --preprocessed_stats                    false
% 1.96/1.02  
% 1.96/1.02  ------ Abstraction refinement Options
% 1.96/1.02  
% 1.96/1.02  --abstr_ref                             []
% 1.96/1.02  --abstr_ref_prep                        false
% 1.96/1.02  --abstr_ref_until_sat                   false
% 1.96/1.02  --abstr_ref_sig_restrict                funpre
% 1.96/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.02  --abstr_ref_under                       []
% 1.96/1.02  
% 1.96/1.02  ------ SAT Options
% 1.96/1.02  
% 1.96/1.02  --sat_mode                              false
% 1.96/1.02  --sat_fm_restart_options                ""
% 1.96/1.02  --sat_gr_def                            false
% 1.96/1.02  --sat_epr_types                         true
% 1.96/1.02  --sat_non_cyclic_types                  false
% 1.96/1.02  --sat_finite_models                     false
% 1.96/1.02  --sat_fm_lemmas                         false
% 1.96/1.02  --sat_fm_prep                           false
% 1.96/1.02  --sat_fm_uc_incr                        true
% 1.96/1.02  --sat_out_model                         small
% 1.96/1.02  --sat_out_clauses                       false
% 1.96/1.02  
% 1.96/1.02  ------ QBF Options
% 1.96/1.02  
% 1.96/1.02  --qbf_mode                              false
% 1.96/1.02  --qbf_elim_univ                         false
% 1.96/1.02  --qbf_dom_inst                          none
% 1.96/1.02  --qbf_dom_pre_inst                      false
% 1.96/1.02  --qbf_sk_in                             false
% 1.96/1.02  --qbf_pred_elim                         true
% 1.96/1.02  --qbf_split                             512
% 1.96/1.02  
% 1.96/1.02  ------ BMC1 Options
% 1.96/1.02  
% 1.96/1.02  --bmc1_incremental                      false
% 1.96/1.02  --bmc1_axioms                           reachable_all
% 1.96/1.02  --bmc1_min_bound                        0
% 1.96/1.02  --bmc1_max_bound                        -1
% 1.96/1.02  --bmc1_max_bound_default                -1
% 1.96/1.02  --bmc1_symbol_reachability              true
% 1.96/1.02  --bmc1_property_lemmas                  false
% 1.96/1.02  --bmc1_k_induction                      false
% 1.96/1.02  --bmc1_non_equiv_states                 false
% 1.96/1.02  --bmc1_deadlock                         false
% 1.96/1.02  --bmc1_ucm                              false
% 1.96/1.02  --bmc1_add_unsat_core                   none
% 1.96/1.02  --bmc1_unsat_core_children              false
% 1.96/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.02  --bmc1_out_stat                         full
% 1.96/1.02  --bmc1_ground_init                      false
% 1.96/1.02  --bmc1_pre_inst_next_state              false
% 1.96/1.02  --bmc1_pre_inst_state                   false
% 1.96/1.02  --bmc1_pre_inst_reach_state             false
% 1.96/1.02  --bmc1_out_unsat_core                   false
% 1.96/1.02  --bmc1_aig_witness_out                  false
% 1.96/1.02  --bmc1_verbose                          false
% 1.96/1.02  --bmc1_dump_clauses_tptp                false
% 1.96/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.02  --bmc1_dump_file                        -
% 1.96/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.02  --bmc1_ucm_extend_mode                  1
% 1.96/1.02  --bmc1_ucm_init_mode                    2
% 1.96/1.02  --bmc1_ucm_cone_mode                    none
% 1.96/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.02  --bmc1_ucm_relax_model                  4
% 1.96/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.02  --bmc1_ucm_layered_model                none
% 1.96/1.02  --bmc1_ucm_max_lemma_size               10
% 1.96/1.02  
% 1.96/1.02  ------ AIG Options
% 1.96/1.02  
% 1.96/1.02  --aig_mode                              false
% 1.96/1.02  
% 1.96/1.02  ------ Instantiation Options
% 1.96/1.02  
% 1.96/1.02  --instantiation_flag                    true
% 1.96/1.02  --inst_sos_flag                         false
% 1.96/1.02  --inst_sos_phase                        true
% 1.96/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.02  --inst_lit_sel_side                     none
% 1.96/1.02  --inst_solver_per_active                1400
% 1.96/1.02  --inst_solver_calls_frac                1.
% 1.96/1.02  --inst_passive_queue_type               priority_queues
% 1.96/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.02  --inst_passive_queues_freq              [25;2]
% 1.96/1.02  --inst_dismatching                      true
% 1.96/1.02  --inst_eager_unprocessed_to_passive     true
% 1.96/1.02  --inst_prop_sim_given                   true
% 1.96/1.02  --inst_prop_sim_new                     false
% 1.96/1.02  --inst_subs_new                         false
% 1.96/1.02  --inst_eq_res_simp                      false
% 1.96/1.02  --inst_subs_given                       false
% 1.96/1.02  --inst_orphan_elimination               true
% 1.96/1.02  --inst_learning_loop_flag               true
% 1.96/1.02  --inst_learning_start                   3000
% 1.96/1.02  --inst_learning_factor                  2
% 1.96/1.02  --inst_start_prop_sim_after_learn       3
% 1.96/1.02  --inst_sel_renew                        solver
% 1.96/1.02  --inst_lit_activity_flag                true
% 1.96/1.02  --inst_restr_to_given                   false
% 1.96/1.02  --inst_activity_threshold               500
% 1.96/1.02  --inst_out_proof                        true
% 1.96/1.02  
% 1.96/1.02  ------ Resolution Options
% 1.96/1.02  
% 1.96/1.02  --resolution_flag                       false
% 1.96/1.02  --res_lit_sel                           adaptive
% 1.96/1.02  --res_lit_sel_side                      none
% 1.96/1.02  --res_ordering                          kbo
% 1.96/1.02  --res_to_prop_solver                    active
% 1.96/1.02  --res_prop_simpl_new                    false
% 1.96/1.02  --res_prop_simpl_given                  true
% 1.96/1.02  --res_passive_queue_type                priority_queues
% 1.96/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.02  --res_passive_queues_freq               [15;5]
% 1.96/1.02  --res_forward_subs                      full
% 1.96/1.02  --res_backward_subs                     full
% 1.96/1.02  --res_forward_subs_resolution           true
% 1.96/1.02  --res_backward_subs_resolution          true
% 1.96/1.02  --res_orphan_elimination                true
% 1.96/1.02  --res_time_limit                        2.
% 1.96/1.02  --res_out_proof                         true
% 1.96/1.02  
% 1.96/1.02  ------ Superposition Options
% 1.96/1.02  
% 1.96/1.02  --superposition_flag                    true
% 1.96/1.02  --sup_passive_queue_type                priority_queues
% 1.96/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.02  --demod_completeness_check              fast
% 1.96/1.02  --demod_use_ground                      true
% 1.96/1.02  --sup_to_prop_solver                    passive
% 1.96/1.02  --sup_prop_simpl_new                    true
% 1.96/1.02  --sup_prop_simpl_given                  true
% 1.96/1.02  --sup_fun_splitting                     false
% 1.96/1.02  --sup_smt_interval                      50000
% 1.96/1.02  
% 1.96/1.02  ------ Superposition Simplification Setup
% 1.96/1.02  
% 1.96/1.02  --sup_indices_passive                   []
% 1.96/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.02  --sup_full_bw                           [BwDemod]
% 1.96/1.02  --sup_immed_triv                        [TrivRules]
% 1.96/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.02  --sup_immed_bw_main                     []
% 1.96/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.02  
% 1.96/1.02  ------ Combination Options
% 1.96/1.02  
% 1.96/1.02  --comb_res_mult                         3
% 1.96/1.02  --comb_sup_mult                         2
% 1.96/1.02  --comb_inst_mult                        10
% 1.96/1.02  
% 1.96/1.02  ------ Debug Options
% 1.96/1.02  
% 1.96/1.02  --dbg_backtrace                         false
% 1.96/1.02  --dbg_dump_prop_clauses                 false
% 1.96/1.02  --dbg_dump_prop_clauses_file            -
% 1.96/1.02  --dbg_out_stat                          false
% 1.96/1.02  
% 1.96/1.02  
% 1.96/1.02  
% 1.96/1.02  
% 1.96/1.02  ------ Proving...
% 1.96/1.02  
% 1.96/1.02  
% 1.96/1.02  % SZS status Theorem for theBenchmark.p
% 1.96/1.02  
% 1.96/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.96/1.02  
% 1.96/1.02  fof(f8,conjecture,(
% 1.96/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 1.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.96/1.02  
% 1.96/1.02  fof(f9,negated_conjecture,(
% 1.96/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 1.96/1.02    inference(negated_conjecture,[],[f8])).
% 1.96/1.02  
% 1.96/1.02  fof(f19,plain,(
% 1.96/1.02    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.96/1.02    inference(ennf_transformation,[],[f9])).
% 1.96/1.02  
% 1.96/1.02  fof(f20,plain,(
% 1.96/1.02    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.96/1.02    inference(flattening,[],[f19])).
% 1.96/1.02  
% 1.96/1.02  fof(f37,plain,(
% 1.96/1.02    ( ! [X4,X2,X0,X3] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => (k1_funct_1(X3,sK10) = X4 & r2_hidden(sK10,X2) & r2_hidden(sK10,X0))) )),
% 1.96/1.02    introduced(choice_axiom,[])).
% 1.96/1.02  
% 1.96/1.02  fof(f36,plain,(
% 1.96/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) => (~r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = sK9 & r2_hidden(X5,X2) & r2_hidden(X5,X0)))) )),
% 1.96/1.02    introduced(choice_axiom,[])).
% 1.96/1.02  
% 1.96/1.02  fof(f35,plain,(
% 1.96/1.02    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (~r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7)) & ? [X5] : (k1_funct_1(sK8,X5) = X4 & r2_hidden(X5,sK7) & r2_hidden(X5,sK5))) & k1_xboole_0 != sK6 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 1.96/1.02    introduced(choice_axiom,[])).
% 1.96/1.02  
% 1.96/1.02  fof(f38,plain,(
% 1.96/1.02    (~r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) & (k1_funct_1(sK8,sK10) = sK9 & r2_hidden(sK10,sK7) & r2_hidden(sK10,sK5))) & k1_xboole_0 != sK6 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)),
% 1.96/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9,sK10])],[f20,f37,f36,f35])).
% 1.96/1.02  
% 1.96/1.02  fof(f68,plain,(
% 1.96/1.02    k1_funct_1(sK8,sK10) = sK9),
% 1.96/1.02    inference(cnf_transformation,[],[f38])).
% 1.96/1.02  
% 1.96/1.02  fof(f3,axiom,(
% 1.96/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.96/1.02  
% 1.96/1.02  fof(f11,plain,(
% 1.96/1.02    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.96/1.02    inference(ennf_transformation,[],[f3])).
% 1.96/1.02  
% 1.96/1.02  fof(f12,plain,(
% 1.96/1.02    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.96/1.02    inference(flattening,[],[f11])).
% 1.96/1.02  
% 1.96/1.02  fof(f21,plain,(
% 1.96/1.02    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.96/1.02    inference(nnf_transformation,[],[f12])).
% 1.96/1.02  
% 1.96/1.02  fof(f22,plain,(
% 1.96/1.02    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.96/1.02    inference(rectify,[],[f21])).
% 1.96/1.02  
% 1.96/1.02  fof(f25,plain,(
% 1.96/1.02    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))))),
% 1.96/1.02    introduced(choice_axiom,[])).
% 1.96/1.02  
% 1.96/1.02  fof(f24,plain,(
% 1.96/1.02    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1,X2)) = X3 & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))))) )),
% 1.96/1.02    introduced(choice_axiom,[])).
% 1.96/1.02  
% 1.96/1.02  fof(f23,plain,(
% 1.96/1.02    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK0(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.96/1.02    introduced(choice_axiom,[])).
% 1.96/1.02  
% 1.96/1.02  fof(f26,plain,(
% 1.96/1.02    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2) & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.96/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).
% 1.96/1.02  
% 1.96/1.02  fof(f44,plain,(
% 1.96/1.02    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/1.02    inference(cnf_transformation,[],[f26])).
% 1.96/1.02  
% 1.96/1.02  fof(f70,plain,(
% 1.96/1.02    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/1.02    inference(equality_resolution,[],[f44])).
% 1.96/1.02  
% 1.96/1.02  fof(f71,plain,(
% 1.96/1.02    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.96/1.02    inference(equality_resolution,[],[f70])).
% 1.96/1.02  
% 1.96/1.02  fof(f62,plain,(
% 1.96/1.02    v1_funct_1(sK8)),
% 1.96/1.02    inference(cnf_transformation,[],[f38])).
% 1.96/1.02  
% 1.96/1.02  fof(f1,axiom,(
% 1.96/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.96/1.02  
% 1.96/1.02  fof(f10,plain,(
% 1.96/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.96/1.02    inference(ennf_transformation,[],[f1])).
% 1.96/1.02  
% 1.96/1.02  fof(f39,plain,(
% 1.96/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.96/1.02    inference(cnf_transformation,[],[f10])).
% 1.96/1.02  
% 1.96/1.02  fof(f64,plain,(
% 1.96/1.02    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.96/1.02    inference(cnf_transformation,[],[f38])).
% 1.96/1.02  
% 1.96/1.02  fof(f2,axiom,(
% 1.96/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.96/1.02  
% 1.96/1.02  fof(f40,plain,(
% 1.96/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.96/1.02    inference(cnf_transformation,[],[f2])).
% 1.96/1.02  
% 1.96/1.02  fof(f66,plain,(
% 1.96/1.02    r2_hidden(sK10,sK5)),
% 1.96/1.02    inference(cnf_transformation,[],[f38])).
% 1.96/1.02  
% 1.96/1.02  fof(f63,plain,(
% 1.96/1.02    v1_funct_2(sK8,sK5,sK6)),
% 1.96/1.02    inference(cnf_transformation,[],[f38])).
% 1.96/1.02  
% 1.96/1.02  fof(f7,axiom,(
% 1.96/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.96/1.02  
% 1.96/1.02  fof(f17,plain,(
% 1.96/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/1.02    inference(ennf_transformation,[],[f7])).
% 1.96/1.02  
% 1.96/1.02  fof(f18,plain,(
% 1.96/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/1.02    inference(flattening,[],[f17])).
% 1.96/1.02  
% 1.96/1.02  fof(f34,plain,(
% 1.96/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/1.02    inference(nnf_transformation,[],[f18])).
% 1.96/1.02  
% 1.96/1.02  fof(f56,plain,(
% 1.96/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/1.02    inference(cnf_transformation,[],[f34])).
% 1.96/1.02  
% 1.96/1.02  fof(f65,plain,(
% 1.96/1.02    k1_xboole_0 != sK6),
% 1.96/1.02    inference(cnf_transformation,[],[f38])).
% 1.96/1.02  
% 1.96/1.02  fof(f6,axiom,(
% 1.96/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.96/1.02  
% 1.96/1.02  fof(f16,plain,(
% 1.96/1.02    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.96/1.02    inference(ennf_transformation,[],[f6])).
% 1.96/1.02  
% 1.96/1.02  fof(f29,plain,(
% 1.96/1.02    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.96/1.02    inference(nnf_transformation,[],[f16])).
% 1.96/1.02  
% 1.96/1.02  fof(f30,plain,(
% 1.96/1.02    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.96/1.02    inference(rectify,[],[f29])).
% 1.96/1.02  
% 1.96/1.02  fof(f32,plain,(
% 1.96/1.02    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK4(X1,X2),X6),X2) & r2_hidden(sK4(X1,X2),X1)))),
% 1.96/1.02    introduced(choice_axiom,[])).
% 1.96/1.02  
% 1.96/1.02  fof(f31,plain,(
% 1.96/1.02    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2))),
% 1.96/1.02    introduced(choice_axiom,[])).
% 1.96/1.02  
% 1.96/1.02  fof(f33,plain,(
% 1.96/1.02    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK4(X1,X2),X6),X2) & r2_hidden(sK4(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.96/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f32,f31])).
% 1.96/1.02  
% 1.96/1.02  fof(f55,plain,(
% 1.96/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.96/1.02    inference(cnf_transformation,[],[f33])).
% 1.96/1.02  
% 1.96/1.02  fof(f4,axiom,(
% 1.96/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.96/1.02  
% 1.96/1.02  fof(f13,plain,(
% 1.96/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.96/1.02    inference(ennf_transformation,[],[f4])).
% 1.96/1.02  
% 1.96/1.02  fof(f14,plain,(
% 1.96/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.96/1.02    inference(flattening,[],[f13])).
% 1.96/1.02  
% 1.96/1.02  fof(f27,plain,(
% 1.96/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.96/1.02    inference(nnf_transformation,[],[f14])).
% 1.96/1.02  
% 1.96/1.02  fof(f28,plain,(
% 1.96/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.96/1.02    inference(flattening,[],[f27])).
% 1.96/1.02  
% 1.96/1.02  fof(f49,plain,(
% 1.96/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.96/1.02    inference(cnf_transformation,[],[f28])).
% 1.96/1.02  
% 1.96/1.02  fof(f5,axiom,(
% 1.96/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.96/1.02  
% 1.96/1.02  fof(f15,plain,(
% 1.96/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.96/1.02    inference(ennf_transformation,[],[f5])).
% 1.96/1.02  
% 1.96/1.02  fof(f52,plain,(
% 1.96/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.96/1.02    inference(cnf_transformation,[],[f15])).
% 1.96/1.02  
% 1.96/1.02  fof(f69,plain,(
% 1.96/1.02    ~r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 1.96/1.02    inference(cnf_transformation,[],[f38])).
% 1.96/1.02  
% 1.96/1.02  fof(f67,plain,(
% 1.96/1.02    r2_hidden(sK10,sK7)),
% 1.96/1.02    inference(cnf_transformation,[],[f38])).
% 1.96/1.02  
% 1.96/1.02  cnf(c_24,negated_conjecture,
% 1.96/1.02      ( k1_funct_1(sK8,sK10) = sK9 ),
% 1.96/1.02      inference(cnf_transformation,[],[f68]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_6,plain,
% 1.96/1.02      ( ~ r2_hidden(X0,X1)
% 1.96/1.02      | ~ r2_hidden(X0,k1_relat_1(X2))
% 1.96/1.02      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 1.96/1.02      | ~ v1_funct_1(X2)
% 1.96/1.02      | ~ v1_relat_1(X2) ),
% 1.96/1.02      inference(cnf_transformation,[],[f71]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_30,negated_conjecture,
% 1.96/1.02      ( v1_funct_1(sK8) ),
% 1.96/1.02      inference(cnf_transformation,[],[f62]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_632,plain,
% 1.96/1.02      ( ~ r2_hidden(X0,X1)
% 1.96/1.02      | ~ r2_hidden(X0,k1_relat_1(X2))
% 1.96/1.02      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 1.96/1.02      | ~ v1_relat_1(X2)
% 1.96/1.02      | sK8 != X2 ),
% 1.96/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_30]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_633,plain,
% 1.96/1.02      ( ~ r2_hidden(X0,X1)
% 1.96/1.02      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 1.96/1.02      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
% 1.96/1.02      | ~ v1_relat_1(sK8) ),
% 1.96/1.02      inference(unflattening,[status(thm)],[c_632]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1303,plain,
% 1.96/1.02      ( r2_hidden(X0,X1) != iProver_top
% 1.96/1.02      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 1.96/1.02      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
% 1.96/1.02      | v1_relat_1(sK8) != iProver_top ),
% 1.96/1.02      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_634,plain,
% 1.96/1.02      ( r2_hidden(X0,X1) != iProver_top
% 1.96/1.02      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 1.96/1.02      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
% 1.96/1.02      | v1_relat_1(sK8) != iProver_top ),
% 1.96/1.02      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_973,plain,( X0 = X0 ),theory(equality) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1517,plain,
% 1.96/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 1.96/1.02      inference(instantiation,[status(thm)],[c_973]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_0,plain,
% 1.96/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.96/1.02      | ~ v1_relat_1(X1)
% 1.96/1.02      | v1_relat_1(X0) ),
% 1.96/1.02      inference(cnf_transformation,[],[f39]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_28,negated_conjecture,
% 1.96/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 1.96/1.02      inference(cnf_transformation,[],[f64]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_322,plain,
% 1.96/1.02      ( ~ v1_relat_1(X0)
% 1.96/1.02      | v1_relat_1(X1)
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X0)
% 1.96/1.02      | sK8 != X1 ),
% 1.96/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_323,plain,
% 1.96/1.02      ( ~ v1_relat_1(X0)
% 1.96/1.02      | v1_relat_1(sK8)
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(X0) ),
% 1.96/1.02      inference(unflattening,[status(thm)],[c_322]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1512,plain,
% 1.96/1.02      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 1.96/1.02      | v1_relat_1(sK8)
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.96/1.02      inference(instantiation,[status(thm)],[c_323]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1597,plain,
% 1.96/1.02      ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | v1_relat_1(sK8)
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 1.96/1.02      inference(instantiation,[status(thm)],[c_1512]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1598,plain,
% 1.96/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 1.96/1.02      | v1_relat_1(sK8) = iProver_top ),
% 1.96/1.02      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1,plain,
% 1.96/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.96/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1653,plain,
% 1.96/1.02      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
% 1.96/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1654,plain,
% 1.96/1.02      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 1.96/1.02      inference(predicate_to_equality,[status(thm)],[c_1653]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_2403,plain,
% 1.96/1.02      ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
% 1.96/1.02      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 1.96/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 1.96/1.02      inference(global_propositional_subsumption,
% 1.96/1.02                [status(thm)],
% 1.96/1.02                [c_1303,c_634,c_1517,c_1598,c_1654]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_2404,plain,
% 1.96/1.02      ( r2_hidden(X0,X1) != iProver_top
% 1.96/1.02      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 1.96/1.02      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
% 1.96/1.02      inference(renaming,[status(thm)],[c_2403]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_2412,plain,
% 1.96/1.02      ( r2_hidden(sK10,X0) != iProver_top
% 1.96/1.02      | r2_hidden(sK10,k1_relat_1(sK8)) != iProver_top
% 1.96/1.02      | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
% 1.96/1.02      inference(superposition,[status(thm)],[c_24,c_2404]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_26,negated_conjecture,
% 1.96/1.02      ( r2_hidden(sK10,sK5) ),
% 1.96/1.02      inference(cnf_transformation,[],[f66]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_34,plain,
% 1.96/1.02      ( r2_hidden(sK10,sK5) = iProver_top ),
% 1.96/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_29,negated_conjecture,
% 1.96/1.02      ( v1_funct_2(sK8,sK5,sK6) ),
% 1.96/1.02      inference(cnf_transformation,[],[f63]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_22,plain,
% 1.96/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.96/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.96/1.02      | k1_xboole_0 = X2 ),
% 1.96/1.02      inference(cnf_transformation,[],[f56]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_337,plain,
% 1.96/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.96/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | sK8 != X0
% 1.96/1.02      | k1_xboole_0 = X2 ),
% 1.96/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_338,plain,
% 1.96/1.02      ( ~ v1_funct_2(sK8,X0,X1)
% 1.96/1.02      | k1_relset_1(X0,X1,sK8) = X0
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | k1_xboole_0 = X1 ),
% 1.96/1.02      inference(unflattening,[status(thm)],[c_337]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_787,plain,
% 1.96/1.02      ( k1_relset_1(X0,X1,sK8) = X0
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | sK8 != sK8
% 1.96/1.02      | sK6 != X1
% 1.96/1.02      | sK5 != X0
% 1.96/1.02      | k1_xboole_0 = X1 ),
% 1.96/1.02      inference(resolution_lifted,[status(thm)],[c_29,c_338]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_788,plain,
% 1.96/1.02      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | k1_xboole_0 = sK6 ),
% 1.96/1.02      inference(unflattening,[status(thm)],[c_787]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_27,negated_conjecture,
% 1.96/1.02      ( k1_xboole_0 != sK6 ),
% 1.96/1.02      inference(cnf_transformation,[],[f65]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_789,plain,
% 1.96/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | k1_relset_1(sK5,sK6,sK8) = sK5 ),
% 1.96/1.02      inference(global_propositional_subsumption,
% 1.96/1.02                [status(thm)],
% 1.96/1.02                [c_788,c_27]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_790,plain,
% 1.96/1.02      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 1.96/1.02      inference(renaming,[status(thm)],[c_789]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_858,plain,
% 1.96/1.02      ( k1_relset_1(sK5,sK6,sK8) = sK5 ),
% 1.96/1.02      inference(equality_resolution_simp,[status(thm)],[c_790]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_14,plain,
% 1.96/1.02      ( ~ r2_hidden(X0,X1)
% 1.96/1.02      | r2_hidden(k4_tarski(X0,sK3(X2,X0)),X2)
% 1.96/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.96/1.02      | k1_relset_1(X1,X3,X2) != X1 ),
% 1.96/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_382,plain,
% 1.96/1.02      ( ~ r2_hidden(X0,X1)
% 1.96/1.02      | r2_hidden(k4_tarski(X0,sK3(X2,X0)),X2)
% 1.96/1.02      | k1_relset_1(X1,X3,X2) != X1
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | sK8 != X2 ),
% 1.96/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_383,plain,
% 1.96/1.02      ( ~ r2_hidden(X0,X1)
% 1.96/1.02      | r2_hidden(k4_tarski(X0,sK3(sK8,X0)),sK8)
% 1.96/1.02      | k1_relset_1(X1,X2,sK8) != X1
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 1.96/1.02      inference(unflattening,[status(thm)],[c_382]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1507,plain,
% 1.96/1.02      ( r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8)
% 1.96/1.02      | ~ r2_hidden(sK10,sK5)
% 1.96/1.02      | k1_relset_1(sK5,X0,sK8) != sK5
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK5,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 1.96/1.02      inference(instantiation,[status(thm)],[c_383]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1631,plain,
% 1.96/1.02      ( r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8)
% 1.96/1.02      | ~ r2_hidden(sK10,sK5)
% 1.96/1.02      | k1_relset_1(sK5,sK6,sK8) != sK5
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 1.96/1.02      inference(instantiation,[status(thm)],[c_1507]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1632,plain,
% 1.96/1.02      ( k1_relset_1(sK5,sK6,sK8) != sK5
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8) = iProver_top
% 1.96/1.02      | r2_hidden(sK10,sK5) != iProver_top ),
% 1.96/1.02      inference(predicate_to_equality,[status(thm)],[c_1631]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_12,plain,
% 1.96/1.02      ( r2_hidden(X0,k1_relat_1(X1))
% 1.96/1.02      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 1.96/1.02      | ~ v1_funct_1(X1)
% 1.96/1.02      | ~ v1_relat_1(X1) ),
% 1.96/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_542,plain,
% 1.96/1.02      ( r2_hidden(X0,k1_relat_1(X1))
% 1.96/1.02      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 1.96/1.02      | ~ v1_relat_1(X1)
% 1.96/1.02      | sK8 != X1 ),
% 1.96/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_543,plain,
% 1.96/1.02      ( r2_hidden(X0,k1_relat_1(sK8))
% 1.96/1.02      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 1.96/1.02      | ~ v1_relat_1(sK8) ),
% 1.96/1.02      inference(unflattening,[status(thm)],[c_542]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1751,plain,
% 1.96/1.02      ( ~ r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8)
% 1.96/1.02      | r2_hidden(sK10,k1_relat_1(sK8))
% 1.96/1.02      | ~ v1_relat_1(sK8) ),
% 1.96/1.02      inference(instantiation,[status(thm)],[c_543]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1752,plain,
% 1.96/1.02      ( r2_hidden(k4_tarski(sK10,sK3(sK8,sK10)),sK8) != iProver_top
% 1.96/1.02      | r2_hidden(sK10,k1_relat_1(sK8)) = iProver_top
% 1.96/1.02      | v1_relat_1(sK8) != iProver_top ),
% 1.96/1.02      inference(predicate_to_equality,[status(thm)],[c_1751]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_2433,plain,
% 1.96/1.02      ( r2_hidden(sK10,X0) != iProver_top
% 1.96/1.02      | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
% 1.96/1.02      inference(global_propositional_subsumption,
% 1.96/1.02                [status(thm)],
% 1.96/1.02                [c_2412,c_34,c_858,c_1517,c_1598,c_1632,c_1654,c_1752]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_13,plain,
% 1.96/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.96/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.96/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_373,plain,
% 1.96/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 1.96/1.02      | sK8 != X2 ),
% 1.96/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_374,plain,
% 1.96/1.02      ( k7_relset_1(X0,X1,sK8,X2) = k9_relat_1(sK8,X2)
% 1.96/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 1.96/1.02      inference(unflattening,[status(thm)],[c_373]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1538,plain,
% 1.96/1.02      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 1.96/1.02      inference(equality_resolution,[status(thm)],[c_374]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_23,negated_conjecture,
% 1.96/1.02      ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 1.96/1.02      inference(cnf_transformation,[],[f69]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1316,plain,
% 1.96/1.02      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
% 1.96/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_1625,plain,
% 1.96/1.02      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
% 1.96/1.02      inference(demodulation,[status(thm)],[c_1538,c_1316]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_2442,plain,
% 1.96/1.02      ( r2_hidden(sK10,sK7) != iProver_top ),
% 1.96/1.02      inference(superposition,[status(thm)],[c_2433,c_1625]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_25,negated_conjecture,
% 1.96/1.02      ( r2_hidden(sK10,sK7) ),
% 1.96/1.02      inference(cnf_transformation,[],[f67]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(c_35,plain,
% 1.96/1.02      ( r2_hidden(sK10,sK7) = iProver_top ),
% 1.96/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.96/1.02  
% 1.96/1.02  cnf(contradiction,plain,
% 1.96/1.02      ( $false ),
% 1.96/1.02      inference(minisat,[status(thm)],[c_2442,c_35]) ).
% 1.96/1.02  
% 1.96/1.02  
% 1.96/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.96/1.02  
% 1.96/1.02  ------                               Statistics
% 1.96/1.02  
% 1.96/1.02  ------ General
% 1.96/1.02  
% 1.96/1.02  abstr_ref_over_cycles:                  0
% 1.96/1.02  abstr_ref_under_cycles:                 0
% 1.96/1.02  gc_basic_clause_elim:                   0
% 1.96/1.02  forced_gc_time:                         0
% 1.96/1.02  parsing_time:                           0.009
% 1.96/1.02  unif_index_cands_time:                  0.
% 1.96/1.02  unif_index_add_time:                    0.
% 1.96/1.02  orderings_time:                         0.
% 1.96/1.02  out_proof_time:                         0.022
% 1.96/1.02  total_time:                             0.107
% 1.96/1.02  num_of_symbols:                         56
% 1.96/1.02  num_of_terms:                           2458
% 1.96/1.02  
% 1.96/1.02  ------ Preprocessing
% 1.96/1.02  
% 1.96/1.02  num_of_splits:                          0
% 1.96/1.02  num_of_split_atoms:                     0
% 1.96/1.02  num_of_reused_defs:                     0
% 1.96/1.02  num_eq_ax_congr_red:                    36
% 1.96/1.02  num_of_sem_filtered_clauses:            1
% 1.96/1.02  num_of_subtypes:                        0
% 1.96/1.02  monotx_restored_types:                  0
% 1.96/1.02  sat_num_of_epr_types:                   0
% 1.96/1.02  sat_num_of_non_cyclic_types:            0
% 1.96/1.02  sat_guarded_non_collapsed_types:        0
% 1.96/1.02  num_pure_diseq_elim:                    0
% 1.96/1.02  simp_replaced_by:                       0
% 1.96/1.02  res_preprocessed:                       141
% 1.96/1.02  prep_upred:                             0
% 1.96/1.02  prep_unflattend:                        38
% 1.96/1.02  smt_new_axioms:                         0
% 1.96/1.02  pred_elim_cands:                        2
% 1.96/1.02  pred_elim:                              3
% 1.96/1.02  pred_elim_cl:                           6
% 1.96/1.02  pred_elim_cycles:                       5
% 1.96/1.02  merged_defs:                            0
% 1.96/1.02  merged_defs_ncl:                        0
% 1.96/1.02  bin_hyper_res:                          0
% 1.96/1.02  prep_cycles:                            4
% 1.96/1.02  pred_elim_time:                         0.007
% 1.96/1.02  splitting_time:                         0.
% 1.96/1.02  sem_filter_time:                        0.
% 1.96/1.02  monotx_time:                            0.
% 1.96/1.02  subtype_inf_time:                       0.
% 1.96/1.02  
% 1.96/1.02  ------ Problem properties
% 1.96/1.02  
% 1.96/1.02  clauses:                                25
% 1.96/1.02  conjectures:                            5
% 1.96/1.02  epr:                                    3
% 1.96/1.02  horn:                                   20
% 1.96/1.02  ground:                                 8
% 1.96/1.02  unary:                                  7
% 1.96/1.02  binary:                                 1
% 1.96/1.02  lits:                                   69
% 1.96/1.02  lits_eq:                                27
% 1.96/1.02  fd_pure:                                0
% 1.96/1.02  fd_pseudo:                              0
% 1.96/1.02  fd_cond:                                0
% 1.96/1.02  fd_pseudo_cond:                         5
% 1.96/1.02  ac_symbols:                             0
% 1.96/1.02  
% 1.96/1.02  ------ Propositional Solver
% 1.96/1.02  
% 1.96/1.02  prop_solver_calls:                      26
% 1.96/1.02  prop_fast_solver_calls:                 973
% 1.96/1.02  smt_solver_calls:                       0
% 1.96/1.02  smt_fast_solver_calls:                  0
% 1.96/1.02  prop_num_of_clauses:                    741
% 1.96/1.02  prop_preprocess_simplified:             4033
% 1.96/1.02  prop_fo_subsumed:                       18
% 1.96/1.02  prop_solver_time:                       0.
% 1.96/1.02  smt_solver_time:                        0.
% 1.96/1.02  smt_fast_solver_time:                   0.
% 1.96/1.02  prop_fast_solver_time:                  0.
% 1.96/1.02  prop_unsat_core_time:                   0.
% 1.96/1.02  
% 1.96/1.02  ------ QBF
% 1.96/1.02  
% 1.96/1.02  qbf_q_res:                              0
% 1.96/1.02  qbf_num_tautologies:                    0
% 1.96/1.02  qbf_prep_cycles:                        0
% 1.96/1.02  
% 1.96/1.02  ------ BMC1
% 1.96/1.02  
% 1.96/1.02  bmc1_current_bound:                     -1
% 1.96/1.02  bmc1_last_solved_bound:                 -1
% 1.96/1.02  bmc1_unsat_core_size:                   -1
% 1.96/1.02  bmc1_unsat_core_parents_size:           -1
% 1.96/1.02  bmc1_merge_next_fun:                    0
% 1.96/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.96/1.02  
% 1.96/1.02  ------ Instantiation
% 1.96/1.02  
% 1.96/1.02  inst_num_of_clauses:                    200
% 1.96/1.02  inst_num_in_passive:                    67
% 1.96/1.02  inst_num_in_active:                     112
% 1.96/1.02  inst_num_in_unprocessed:                21
% 1.96/1.02  inst_num_of_loops:                      140
% 1.96/1.02  inst_num_of_learning_restarts:          0
% 1.96/1.02  inst_num_moves_active_passive:          25
% 1.96/1.02  inst_lit_activity:                      0
% 1.96/1.02  inst_lit_activity_moves:                0
% 1.96/1.02  inst_num_tautologies:                   0
% 1.96/1.02  inst_num_prop_implied:                  0
% 1.96/1.02  inst_num_existing_simplified:           0
% 1.96/1.02  inst_num_eq_res_simplified:             0
% 1.96/1.02  inst_num_child_elim:                    0
% 1.96/1.02  inst_num_of_dismatching_blockings:      20
% 1.96/1.02  inst_num_of_non_proper_insts:           133
% 1.96/1.02  inst_num_of_duplicates:                 0
% 1.96/1.02  inst_inst_num_from_inst_to_res:         0
% 1.96/1.02  inst_dismatching_checking_time:         0.
% 1.96/1.02  
% 1.96/1.02  ------ Resolution
% 1.96/1.02  
% 1.96/1.02  res_num_of_clauses:                     0
% 1.96/1.02  res_num_in_passive:                     0
% 1.96/1.02  res_num_in_active:                      0
% 1.96/1.02  res_num_of_loops:                       145
% 1.96/1.02  res_forward_subset_subsumed:            17
% 1.96/1.02  res_backward_subset_subsumed:           0
% 1.96/1.02  res_forward_subsumed:                   0
% 1.96/1.02  res_backward_subsumed:                  0
% 1.96/1.02  res_forward_subsumption_resolution:     0
% 1.96/1.02  res_backward_subsumption_resolution:    0
% 1.96/1.02  res_clause_to_clause_subsumption:       52
% 1.96/1.02  res_orphan_elimination:                 0
% 1.96/1.02  res_tautology_del:                      23
% 1.96/1.02  res_num_eq_res_simplified:              1
% 1.96/1.02  res_num_sel_changes:                    0
% 1.96/1.02  res_moves_from_active_to_pass:          0
% 1.96/1.02  
% 1.96/1.02  ------ Superposition
% 1.96/1.02  
% 1.96/1.02  sup_time_total:                         0.
% 1.96/1.02  sup_time_generating:                    0.
% 1.96/1.02  sup_time_sim_full:                      0.
% 1.96/1.02  sup_time_sim_immed:                     0.
% 1.96/1.02  
% 1.96/1.02  sup_num_of_clauses:                     37
% 1.96/1.02  sup_num_in_active:                      27
% 1.96/1.02  sup_num_in_passive:                     10
% 1.96/1.02  sup_num_of_loops:                       27
% 1.96/1.02  sup_fw_superposition:                   2
% 1.96/1.02  sup_bw_superposition:                   12
% 1.96/1.02  sup_immediate_simplified:               2
% 1.96/1.02  sup_given_eliminated:                   0
% 1.96/1.02  comparisons_done:                       0
% 1.96/1.02  comparisons_avoided:                    2
% 1.96/1.02  
% 1.96/1.02  ------ Simplifications
% 1.96/1.02  
% 1.96/1.02  
% 1.96/1.02  sim_fw_subset_subsumed:                 2
% 1.96/1.02  sim_bw_subset_subsumed:                 0
% 1.96/1.02  sim_fw_subsumed:                        0
% 1.96/1.02  sim_bw_subsumed:                        0
% 1.96/1.02  sim_fw_subsumption_res:                 0
% 1.96/1.02  sim_bw_subsumption_res:                 0
% 1.96/1.02  sim_tautology_del:                      1
% 1.96/1.02  sim_eq_tautology_del:                   1
% 1.96/1.02  sim_eq_res_simp:                        0
% 1.96/1.02  sim_fw_demodulated:                     0
% 1.96/1.02  sim_bw_demodulated:                     1
% 1.96/1.02  sim_light_normalised:                   0
% 1.96/1.02  sim_joinable_taut:                      0
% 1.96/1.02  sim_joinable_simp:                      0
% 1.96/1.02  sim_ac_normalised:                      0
% 1.96/1.02  sim_smt_subsumption:                    0
% 1.96/1.02  
%------------------------------------------------------------------------------

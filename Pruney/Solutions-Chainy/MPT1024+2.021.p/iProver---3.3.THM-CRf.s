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
% DateTime   : Thu Dec  3 12:07:51 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 425 expanded)
%              Number of clauses        :   79 ( 126 expanded)
%              Number of leaves         :   18 ( 108 expanded)
%              Depth                    :   22
%              Number of atoms          :  500 (2422 expanded)
%              Number of equality atoms :  177 ( 555 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f36,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ r2_hidden(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f24,f38,f37])).

fof(f66,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

fof(f30,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).

fof(f47,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f65,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f39])).

fof(f48,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f69,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_943,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X2
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_944,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_946,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_27])).

cnf(c_2075,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2079,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3191,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2075,c_2079])).

cnf(c_3295,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_946,c_3191])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_661,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_662,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),X1)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_2068,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_32,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_663,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2287,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2288,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2287])).

cnf(c_2344,plain,
    ( r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2068,c_32,c_663,c_2288])).

cnf(c_2345,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2344])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_646,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_647,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_2069,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_648,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_2357,plain,
    ( r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2069,c_32,c_648,c_2288])).

cnf(c_2358,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2357])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2086,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3959,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X2) = iProver_top
    | r1_tarski(k1_relat_1(sK7),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2358,c_2086])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2078,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2996,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_2075,c_2078])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2076,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3460,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2996,c_2076])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_676,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_677,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_2067,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_678,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_2312,plain,
    ( r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_32,c_678,c_2288])).

cnf(c_2313,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2312])).

cnf(c_3470,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
    inference(superposition,[status(thm)],[c_3460,c_2313])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2077,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3645,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3470,c_2077])).

cnf(c_6076,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3959,c_3645])).

cnf(c_6810,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6076,c_3460])).

cnf(c_6816,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2345,c_6810])).

cnf(c_6876,plain,
    ( r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6816,c_3460])).

cnf(c_6881,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3295,c_6876])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2577,plain,
    ( r1_tarski(k1_xboole_0,sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2387,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
    | r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2969,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2321,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2970,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_2321])).

cnf(c_2296,plain,
    ( r2_hidden(sK8,X0)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | ~ r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3287,plain,
    ( ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | r2_hidden(sK8,sK5)
    | ~ r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2589,plain,
    ( ~ r2_hidden(sK8,X0)
    | ~ r1_tarski(X0,sK8) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4396,plain,
    ( ~ r2_hidden(sK8,sK5)
    | ~ r1_tarski(sK5,sK8) ),
    inference(instantiation,[status(thm)],[c_2589])).

cnf(c_1474,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2582,plain,
    ( ~ r1_tarski(X0,sK8)
    | r1_tarski(X1,sK8)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_5182,plain,
    ( ~ r1_tarski(X0,sK8)
    | r1_tarski(sK5,sK8)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2582])).

cnf(c_5184,plain,
    ( r1_tarski(sK5,sK8)
    | ~ r1_tarski(k1_xboole_0,sK8)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5182])).

cnf(c_6884,plain,
    ( r1_tarski(sK4,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6881,c_27,c_26,c_2577,c_2969,c_2970,c_3287,c_4396,c_5184])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2087,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2088,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3185,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_2088])).

cnf(c_6889,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6884,c_3185])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:22:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.86/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/0.99  
% 2.86/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.86/0.99  
% 2.86/0.99  ------  iProver source info
% 2.86/0.99  
% 2.86/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.86/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.86/0.99  git: non_committed_changes: false
% 2.86/0.99  git: last_make_outside_of_git: false
% 2.86/0.99  
% 2.86/0.99  ------ 
% 2.86/0.99  
% 2.86/0.99  ------ Input Options
% 2.86/0.99  
% 2.86/0.99  --out_options                           all
% 2.86/0.99  --tptp_safe_out                         true
% 2.86/0.99  --problem_path                          ""
% 2.86/0.99  --include_path                          ""
% 2.86/0.99  --clausifier                            res/vclausify_rel
% 2.86/0.99  --clausifier_options                    --mode clausify
% 2.86/0.99  --stdin                                 false
% 2.86/0.99  --stats_out                             all
% 2.86/0.99  
% 2.86/0.99  ------ General Options
% 2.86/0.99  
% 2.86/0.99  --fof                                   false
% 2.86/0.99  --time_out_real                         305.
% 2.86/0.99  --time_out_virtual                      -1.
% 2.86/0.99  --symbol_type_check                     false
% 2.86/0.99  --clausify_out                          false
% 2.86/0.99  --sig_cnt_out                           false
% 2.86/0.99  --trig_cnt_out                          false
% 2.86/0.99  --trig_cnt_out_tolerance                1.
% 2.86/0.99  --trig_cnt_out_sk_spl                   false
% 2.86/0.99  --abstr_cl_out                          false
% 2.86/0.99  
% 2.86/0.99  ------ Global Options
% 2.86/0.99  
% 2.86/0.99  --schedule                              default
% 2.86/0.99  --add_important_lit                     false
% 2.86/0.99  --prop_solver_per_cl                    1000
% 2.86/0.99  --min_unsat_core                        false
% 2.86/0.99  --soft_assumptions                      false
% 2.86/0.99  --soft_lemma_size                       3
% 2.86/0.99  --prop_impl_unit_size                   0
% 2.86/0.99  --prop_impl_unit                        []
% 2.86/0.99  --share_sel_clauses                     true
% 2.86/0.99  --reset_solvers                         false
% 2.86/0.99  --bc_imp_inh                            [conj_cone]
% 2.86/0.99  --conj_cone_tolerance                   3.
% 2.86/0.99  --extra_neg_conj                        none
% 2.86/0.99  --large_theory_mode                     true
% 2.86/0.99  --prolific_symb_bound                   200
% 2.86/0.99  --lt_threshold                          2000
% 2.86/0.99  --clause_weak_htbl                      true
% 2.86/0.99  --gc_record_bc_elim                     false
% 2.86/0.99  
% 2.86/0.99  ------ Preprocessing Options
% 2.86/0.99  
% 2.86/0.99  --preprocessing_flag                    true
% 2.86/0.99  --time_out_prep_mult                    0.1
% 2.86/0.99  --splitting_mode                        input
% 2.86/0.99  --splitting_grd                         true
% 2.86/0.99  --splitting_cvd                         false
% 2.86/0.99  --splitting_cvd_svl                     false
% 2.86/0.99  --splitting_nvd                         32
% 2.86/0.99  --sub_typing                            true
% 2.86/0.99  --prep_gs_sim                           true
% 2.86/0.99  --prep_unflatten                        true
% 2.86/0.99  --prep_res_sim                          true
% 2.86/0.99  --prep_upred                            true
% 2.86/0.99  --prep_sem_filter                       exhaustive
% 2.86/0.99  --prep_sem_filter_out                   false
% 2.86/0.99  --pred_elim                             true
% 2.86/0.99  --res_sim_input                         true
% 2.86/0.99  --eq_ax_congr_red                       true
% 2.86/0.99  --pure_diseq_elim                       true
% 2.86/0.99  --brand_transform                       false
% 2.86/0.99  --non_eq_to_eq                          false
% 2.86/0.99  --prep_def_merge                        true
% 2.86/0.99  --prep_def_merge_prop_impl              false
% 2.86/0.99  --prep_def_merge_mbd                    true
% 2.86/0.99  --prep_def_merge_tr_red                 false
% 2.86/0.99  --prep_def_merge_tr_cl                  false
% 2.86/0.99  --smt_preprocessing                     true
% 2.86/0.99  --smt_ac_axioms                         fast
% 2.86/0.99  --preprocessed_out                      false
% 2.86/0.99  --preprocessed_stats                    false
% 2.86/0.99  
% 2.86/0.99  ------ Abstraction refinement Options
% 2.86/0.99  
% 2.86/0.99  --abstr_ref                             []
% 2.86/0.99  --abstr_ref_prep                        false
% 2.86/0.99  --abstr_ref_until_sat                   false
% 2.86/0.99  --abstr_ref_sig_restrict                funpre
% 2.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/0.99  --abstr_ref_under                       []
% 2.86/0.99  
% 2.86/0.99  ------ SAT Options
% 2.86/0.99  
% 2.86/0.99  --sat_mode                              false
% 2.86/0.99  --sat_fm_restart_options                ""
% 2.86/0.99  --sat_gr_def                            false
% 2.86/0.99  --sat_epr_types                         true
% 2.86/0.99  --sat_non_cyclic_types                  false
% 2.86/0.99  --sat_finite_models                     false
% 2.86/0.99  --sat_fm_lemmas                         false
% 2.86/0.99  --sat_fm_prep                           false
% 2.86/0.99  --sat_fm_uc_incr                        true
% 2.86/0.99  --sat_out_model                         small
% 2.86/0.99  --sat_out_clauses                       false
% 2.86/0.99  
% 2.86/0.99  ------ QBF Options
% 2.86/0.99  
% 2.86/0.99  --qbf_mode                              false
% 2.86/0.99  --qbf_elim_univ                         false
% 2.86/0.99  --qbf_dom_inst                          none
% 2.86/0.99  --qbf_dom_pre_inst                      false
% 2.86/0.99  --qbf_sk_in                             false
% 2.86/0.99  --qbf_pred_elim                         true
% 2.86/0.99  --qbf_split                             512
% 2.86/0.99  
% 2.86/0.99  ------ BMC1 Options
% 2.86/0.99  
% 2.86/0.99  --bmc1_incremental                      false
% 2.86/0.99  --bmc1_axioms                           reachable_all
% 2.86/0.99  --bmc1_min_bound                        0
% 2.86/0.99  --bmc1_max_bound                        -1
% 2.86/0.99  --bmc1_max_bound_default                -1
% 2.86/0.99  --bmc1_symbol_reachability              true
% 2.86/0.99  --bmc1_property_lemmas                  false
% 2.86/0.99  --bmc1_k_induction                      false
% 2.86/0.99  --bmc1_non_equiv_states                 false
% 2.86/0.99  --bmc1_deadlock                         false
% 2.86/0.99  --bmc1_ucm                              false
% 2.86/0.99  --bmc1_add_unsat_core                   none
% 2.86/0.99  --bmc1_unsat_core_children              false
% 2.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/0.99  --bmc1_out_stat                         full
% 2.86/0.99  --bmc1_ground_init                      false
% 2.86/0.99  --bmc1_pre_inst_next_state              false
% 2.86/0.99  --bmc1_pre_inst_state                   false
% 2.86/0.99  --bmc1_pre_inst_reach_state             false
% 2.86/0.99  --bmc1_out_unsat_core                   false
% 2.86/0.99  --bmc1_aig_witness_out                  false
% 2.86/0.99  --bmc1_verbose                          false
% 2.86/0.99  --bmc1_dump_clauses_tptp                false
% 2.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.86/0.99  --bmc1_dump_file                        -
% 2.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.86/0.99  --bmc1_ucm_extend_mode                  1
% 2.86/0.99  --bmc1_ucm_init_mode                    2
% 2.86/0.99  --bmc1_ucm_cone_mode                    none
% 2.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.86/0.99  --bmc1_ucm_relax_model                  4
% 2.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/0.99  --bmc1_ucm_layered_model                none
% 2.86/0.99  --bmc1_ucm_max_lemma_size               10
% 2.86/0.99  
% 2.86/0.99  ------ AIG Options
% 2.86/0.99  
% 2.86/0.99  --aig_mode                              false
% 2.86/0.99  
% 2.86/0.99  ------ Instantiation Options
% 2.86/0.99  
% 2.86/0.99  --instantiation_flag                    true
% 2.86/0.99  --inst_sos_flag                         false
% 2.86/0.99  --inst_sos_phase                        true
% 2.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/0.99  --inst_lit_sel_side                     num_symb
% 2.86/0.99  --inst_solver_per_active                1400
% 2.86/0.99  --inst_solver_calls_frac                1.
% 2.86/0.99  --inst_passive_queue_type               priority_queues
% 2.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/0.99  --inst_passive_queues_freq              [25;2]
% 2.86/0.99  --inst_dismatching                      true
% 2.86/0.99  --inst_eager_unprocessed_to_passive     true
% 2.86/0.99  --inst_prop_sim_given                   true
% 2.86/0.99  --inst_prop_sim_new                     false
% 2.86/0.99  --inst_subs_new                         false
% 2.86/0.99  --inst_eq_res_simp                      false
% 2.86/0.99  --inst_subs_given                       false
% 2.86/0.99  --inst_orphan_elimination               true
% 2.86/0.99  --inst_learning_loop_flag               true
% 2.86/0.99  --inst_learning_start                   3000
% 2.86/0.99  --inst_learning_factor                  2
% 2.86/0.99  --inst_start_prop_sim_after_learn       3
% 2.86/0.99  --inst_sel_renew                        solver
% 2.86/0.99  --inst_lit_activity_flag                true
% 2.86/0.99  --inst_restr_to_given                   false
% 2.86/0.99  --inst_activity_threshold               500
% 2.86/0.99  --inst_out_proof                        true
% 2.86/0.99  
% 2.86/0.99  ------ Resolution Options
% 2.86/0.99  
% 2.86/0.99  --resolution_flag                       true
% 2.86/0.99  --res_lit_sel                           adaptive
% 2.86/0.99  --res_lit_sel_side                      none
% 2.86/0.99  --res_ordering                          kbo
% 2.86/0.99  --res_to_prop_solver                    active
% 2.86/0.99  --res_prop_simpl_new                    false
% 2.86/0.99  --res_prop_simpl_given                  true
% 2.86/0.99  --res_passive_queue_type                priority_queues
% 2.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/0.99  --res_passive_queues_freq               [15;5]
% 2.86/0.99  --res_forward_subs                      full
% 2.86/0.99  --res_backward_subs                     full
% 2.86/0.99  --res_forward_subs_resolution           true
% 2.86/0.99  --res_backward_subs_resolution          true
% 2.86/0.99  --res_orphan_elimination                true
% 2.86/0.99  --res_time_limit                        2.
% 2.86/0.99  --res_out_proof                         true
% 2.86/0.99  
% 2.86/0.99  ------ Superposition Options
% 2.86/0.99  
% 2.86/0.99  --superposition_flag                    true
% 2.86/0.99  --sup_passive_queue_type                priority_queues
% 2.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.86/0.99  --demod_completeness_check              fast
% 2.86/0.99  --demod_use_ground                      true
% 2.86/0.99  --sup_to_prop_solver                    passive
% 2.86/0.99  --sup_prop_simpl_new                    true
% 2.86/0.99  --sup_prop_simpl_given                  true
% 2.86/0.99  --sup_fun_splitting                     false
% 2.86/0.99  --sup_smt_interval                      50000
% 2.86/0.99  
% 2.86/0.99  ------ Superposition Simplification Setup
% 2.86/0.99  
% 2.86/0.99  --sup_indices_passive                   []
% 2.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.99  --sup_full_bw                           [BwDemod]
% 2.86/0.99  --sup_immed_triv                        [TrivRules]
% 2.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.99  --sup_immed_bw_main                     []
% 2.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.99  
% 2.86/0.99  ------ Combination Options
% 2.86/0.99  
% 2.86/0.99  --comb_res_mult                         3
% 2.86/0.99  --comb_sup_mult                         2
% 2.86/0.99  --comb_inst_mult                        10
% 2.86/0.99  
% 2.86/0.99  ------ Debug Options
% 2.86/0.99  
% 2.86/0.99  --dbg_backtrace                         false
% 2.86/0.99  --dbg_dump_prop_clauses                 false
% 2.86/0.99  --dbg_dump_prop_clauses_file            -
% 2.86/0.99  --dbg_out_stat                          false
% 2.86/0.99  ------ Parsing...
% 2.86/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.86/0.99  
% 2.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.86/0.99  
% 2.86/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.86/0.99  
% 2.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.86/0.99  ------ Proving...
% 2.86/0.99  ------ Problem Properties 
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  clauses                                 25
% 2.86/0.99  conjectures                             3
% 2.86/0.99  EPR                                     3
% 2.86/0.99  Horn                                    19
% 2.86/0.99  unary                                   3
% 2.86/0.99  binary                                  10
% 2.86/0.99  lits                                    67
% 2.86/0.99  lits eq                                 17
% 2.86/0.99  fd_pure                                 0
% 2.86/0.99  fd_pseudo                               0
% 2.86/0.99  fd_cond                                 0
% 2.86/0.99  fd_pseudo_cond                          4
% 2.86/0.99  AC symbols                              0
% 2.86/0.99  
% 2.86/0.99  ------ Schedule dynamic 5 is on 
% 2.86/0.99  
% 2.86/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  ------ 
% 2.86/0.99  Current options:
% 2.86/0.99  ------ 
% 2.86/0.99  
% 2.86/0.99  ------ Input Options
% 2.86/0.99  
% 2.86/0.99  --out_options                           all
% 2.86/0.99  --tptp_safe_out                         true
% 2.86/0.99  --problem_path                          ""
% 2.86/0.99  --include_path                          ""
% 2.86/0.99  --clausifier                            res/vclausify_rel
% 2.86/0.99  --clausifier_options                    --mode clausify
% 2.86/0.99  --stdin                                 false
% 2.86/0.99  --stats_out                             all
% 2.86/0.99  
% 2.86/0.99  ------ General Options
% 2.86/0.99  
% 2.86/0.99  --fof                                   false
% 2.86/0.99  --time_out_real                         305.
% 2.86/0.99  --time_out_virtual                      -1.
% 2.86/0.99  --symbol_type_check                     false
% 2.86/0.99  --clausify_out                          false
% 2.86/0.99  --sig_cnt_out                           false
% 2.86/0.99  --trig_cnt_out                          false
% 2.86/0.99  --trig_cnt_out_tolerance                1.
% 2.86/0.99  --trig_cnt_out_sk_spl                   false
% 2.86/0.99  --abstr_cl_out                          false
% 2.86/0.99  
% 2.86/0.99  ------ Global Options
% 2.86/0.99  
% 2.86/0.99  --schedule                              default
% 2.86/0.99  --add_important_lit                     false
% 2.86/0.99  --prop_solver_per_cl                    1000
% 2.86/0.99  --min_unsat_core                        false
% 2.86/0.99  --soft_assumptions                      false
% 2.86/0.99  --soft_lemma_size                       3
% 2.86/0.99  --prop_impl_unit_size                   0
% 2.86/0.99  --prop_impl_unit                        []
% 2.86/0.99  --share_sel_clauses                     true
% 2.86/0.99  --reset_solvers                         false
% 2.86/0.99  --bc_imp_inh                            [conj_cone]
% 2.86/0.99  --conj_cone_tolerance                   3.
% 2.86/0.99  --extra_neg_conj                        none
% 2.86/0.99  --large_theory_mode                     true
% 2.86/0.99  --prolific_symb_bound                   200
% 2.86/0.99  --lt_threshold                          2000
% 2.86/0.99  --clause_weak_htbl                      true
% 2.86/0.99  --gc_record_bc_elim                     false
% 2.86/0.99  
% 2.86/0.99  ------ Preprocessing Options
% 2.86/0.99  
% 2.86/0.99  --preprocessing_flag                    true
% 2.86/0.99  --time_out_prep_mult                    0.1
% 2.86/0.99  --splitting_mode                        input
% 2.86/0.99  --splitting_grd                         true
% 2.86/0.99  --splitting_cvd                         false
% 2.86/0.99  --splitting_cvd_svl                     false
% 2.86/0.99  --splitting_nvd                         32
% 2.86/0.99  --sub_typing                            true
% 2.86/0.99  --prep_gs_sim                           true
% 2.86/0.99  --prep_unflatten                        true
% 2.86/0.99  --prep_res_sim                          true
% 2.86/0.99  --prep_upred                            true
% 2.86/0.99  --prep_sem_filter                       exhaustive
% 2.86/0.99  --prep_sem_filter_out                   false
% 2.86/0.99  --pred_elim                             true
% 2.86/0.99  --res_sim_input                         true
% 2.86/0.99  --eq_ax_congr_red                       true
% 2.86/0.99  --pure_diseq_elim                       true
% 2.86/0.99  --brand_transform                       false
% 2.86/0.99  --non_eq_to_eq                          false
% 2.86/0.99  --prep_def_merge                        true
% 2.86/0.99  --prep_def_merge_prop_impl              false
% 2.86/0.99  --prep_def_merge_mbd                    true
% 2.86/0.99  --prep_def_merge_tr_red                 false
% 2.86/0.99  --prep_def_merge_tr_cl                  false
% 2.86/0.99  --smt_preprocessing                     true
% 2.86/0.99  --smt_ac_axioms                         fast
% 2.86/0.99  --preprocessed_out                      false
% 2.86/0.99  --preprocessed_stats                    false
% 2.86/0.99  
% 2.86/0.99  ------ Abstraction refinement Options
% 2.86/0.99  
% 2.86/0.99  --abstr_ref                             []
% 2.86/0.99  --abstr_ref_prep                        false
% 2.86/0.99  --abstr_ref_until_sat                   false
% 2.86/0.99  --abstr_ref_sig_restrict                funpre
% 2.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/0.99  --abstr_ref_under                       []
% 2.86/0.99  
% 2.86/0.99  ------ SAT Options
% 2.86/0.99  
% 2.86/0.99  --sat_mode                              false
% 2.86/0.99  --sat_fm_restart_options                ""
% 2.86/0.99  --sat_gr_def                            false
% 2.86/0.99  --sat_epr_types                         true
% 2.86/0.99  --sat_non_cyclic_types                  false
% 2.86/0.99  --sat_finite_models                     false
% 2.86/0.99  --sat_fm_lemmas                         false
% 2.86/0.99  --sat_fm_prep                           false
% 2.86/0.99  --sat_fm_uc_incr                        true
% 2.86/0.99  --sat_out_model                         small
% 2.86/0.99  --sat_out_clauses                       false
% 2.86/0.99  
% 2.86/0.99  ------ QBF Options
% 2.86/0.99  
% 2.86/0.99  --qbf_mode                              false
% 2.86/0.99  --qbf_elim_univ                         false
% 2.86/0.99  --qbf_dom_inst                          none
% 2.86/0.99  --qbf_dom_pre_inst                      false
% 2.86/0.99  --qbf_sk_in                             false
% 2.86/0.99  --qbf_pred_elim                         true
% 2.86/0.99  --qbf_split                             512
% 2.86/0.99  
% 2.86/0.99  ------ BMC1 Options
% 2.86/0.99  
% 2.86/0.99  --bmc1_incremental                      false
% 2.86/0.99  --bmc1_axioms                           reachable_all
% 2.86/0.99  --bmc1_min_bound                        0
% 2.86/0.99  --bmc1_max_bound                        -1
% 2.86/0.99  --bmc1_max_bound_default                -1
% 2.86/0.99  --bmc1_symbol_reachability              true
% 2.86/0.99  --bmc1_property_lemmas                  false
% 2.86/0.99  --bmc1_k_induction                      false
% 2.86/0.99  --bmc1_non_equiv_states                 false
% 2.86/0.99  --bmc1_deadlock                         false
% 2.86/0.99  --bmc1_ucm                              false
% 2.86/0.99  --bmc1_add_unsat_core                   none
% 2.86/0.99  --bmc1_unsat_core_children              false
% 2.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/0.99  --bmc1_out_stat                         full
% 2.86/0.99  --bmc1_ground_init                      false
% 2.86/0.99  --bmc1_pre_inst_next_state              false
% 2.86/0.99  --bmc1_pre_inst_state                   false
% 2.86/0.99  --bmc1_pre_inst_reach_state             false
% 2.86/0.99  --bmc1_out_unsat_core                   false
% 2.86/0.99  --bmc1_aig_witness_out                  false
% 2.86/0.99  --bmc1_verbose                          false
% 2.86/0.99  --bmc1_dump_clauses_tptp                false
% 2.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.86/0.99  --bmc1_dump_file                        -
% 2.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.86/0.99  --bmc1_ucm_extend_mode                  1
% 2.86/0.99  --bmc1_ucm_init_mode                    2
% 2.86/0.99  --bmc1_ucm_cone_mode                    none
% 2.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.86/0.99  --bmc1_ucm_relax_model                  4
% 2.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/0.99  --bmc1_ucm_layered_model                none
% 2.86/0.99  --bmc1_ucm_max_lemma_size               10
% 2.86/0.99  
% 2.86/0.99  ------ AIG Options
% 2.86/0.99  
% 2.86/0.99  --aig_mode                              false
% 2.86/0.99  
% 2.86/0.99  ------ Instantiation Options
% 2.86/0.99  
% 2.86/0.99  --instantiation_flag                    true
% 2.86/0.99  --inst_sos_flag                         false
% 2.86/0.99  --inst_sos_phase                        true
% 2.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/0.99  --inst_lit_sel_side                     none
% 2.86/0.99  --inst_solver_per_active                1400
% 2.86/0.99  --inst_solver_calls_frac                1.
% 2.86/0.99  --inst_passive_queue_type               priority_queues
% 2.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/0.99  --inst_passive_queues_freq              [25;2]
% 2.86/0.99  --inst_dismatching                      true
% 2.86/0.99  --inst_eager_unprocessed_to_passive     true
% 2.86/0.99  --inst_prop_sim_given                   true
% 2.86/0.99  --inst_prop_sim_new                     false
% 2.86/0.99  --inst_subs_new                         false
% 2.86/0.99  --inst_eq_res_simp                      false
% 2.86/0.99  --inst_subs_given                       false
% 2.86/0.99  --inst_orphan_elimination               true
% 2.86/0.99  --inst_learning_loop_flag               true
% 2.86/0.99  --inst_learning_start                   3000
% 2.86/0.99  --inst_learning_factor                  2
% 2.86/0.99  --inst_start_prop_sim_after_learn       3
% 2.86/0.99  --inst_sel_renew                        solver
% 2.86/0.99  --inst_lit_activity_flag                true
% 2.86/0.99  --inst_restr_to_given                   false
% 2.86/0.99  --inst_activity_threshold               500
% 2.86/0.99  --inst_out_proof                        true
% 2.86/0.99  
% 2.86/0.99  ------ Resolution Options
% 2.86/0.99  
% 2.86/0.99  --resolution_flag                       false
% 2.86/0.99  --res_lit_sel                           adaptive
% 2.86/0.99  --res_lit_sel_side                      none
% 2.86/0.99  --res_ordering                          kbo
% 2.86/0.99  --res_to_prop_solver                    active
% 2.86/0.99  --res_prop_simpl_new                    false
% 2.86/0.99  --res_prop_simpl_given                  true
% 2.86/0.99  --res_passive_queue_type                priority_queues
% 2.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/0.99  --res_passive_queues_freq               [15;5]
% 2.86/0.99  --res_forward_subs                      full
% 2.86/0.99  --res_backward_subs                     full
% 2.86/0.99  --res_forward_subs_resolution           true
% 2.86/0.99  --res_backward_subs_resolution          true
% 2.86/0.99  --res_orphan_elimination                true
% 2.86/0.99  --res_time_limit                        2.
% 2.86/0.99  --res_out_proof                         true
% 2.86/0.99  
% 2.86/0.99  ------ Superposition Options
% 2.86/0.99  
% 2.86/0.99  --superposition_flag                    true
% 2.86/0.99  --sup_passive_queue_type                priority_queues
% 2.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.86/0.99  --demod_completeness_check              fast
% 2.86/0.99  --demod_use_ground                      true
% 2.86/0.99  --sup_to_prop_solver                    passive
% 2.86/0.99  --sup_prop_simpl_new                    true
% 2.86/0.99  --sup_prop_simpl_given                  true
% 2.86/0.99  --sup_fun_splitting                     false
% 2.86/0.99  --sup_smt_interval                      50000
% 2.86/0.99  
% 2.86/0.99  ------ Superposition Simplification Setup
% 2.86/0.99  
% 2.86/0.99  --sup_indices_passive                   []
% 2.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.99  --sup_full_bw                           [BwDemod]
% 2.86/0.99  --sup_immed_triv                        [TrivRules]
% 2.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.99  --sup_immed_bw_main                     []
% 2.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.99  
% 2.86/0.99  ------ Combination Options
% 2.86/0.99  
% 2.86/0.99  --comb_res_mult                         3
% 2.86/0.99  --comb_sup_mult                         2
% 2.86/0.99  --comb_inst_mult                        10
% 2.86/0.99  
% 2.86/0.99  ------ Debug Options
% 2.86/0.99  
% 2.86/0.99  --dbg_backtrace                         false
% 2.86/0.99  --dbg_dump_prop_clauses                 false
% 2.86/0.99  --dbg_dump_prop_clauses_file            -
% 2.86/0.99  --dbg_out_stat                          false
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  ------ Proving...
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  % SZS status Theorem for theBenchmark.p
% 2.86/0.99  
% 2.86/0.99   Resolution empty clause
% 2.86/0.99  
% 2.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.86/0.99  
% 2.86/0.99  fof(f10,axiom,(
% 2.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f21,plain,(
% 2.86/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.99    inference(ennf_transformation,[],[f10])).
% 2.86/0.99  
% 2.86/0.99  fof(f22,plain,(
% 2.86/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.99    inference(flattening,[],[f21])).
% 2.86/0.99  
% 2.86/0.99  fof(f36,plain,(
% 2.86/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.99    inference(nnf_transformation,[],[f22])).
% 2.86/0.99  
% 2.86/0.99  fof(f59,plain,(
% 2.86/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/0.99    inference(cnf_transformation,[],[f36])).
% 2.86/0.99  
% 2.86/0.99  fof(f11,conjecture,(
% 2.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f12,negated_conjecture,(
% 2.86/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.86/0.99    inference(negated_conjecture,[],[f11])).
% 2.86/0.99  
% 2.86/0.99  fof(f23,plain,(
% 2.86/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.86/0.99    inference(ennf_transformation,[],[f12])).
% 2.86/0.99  
% 2.86/0.99  fof(f24,plain,(
% 2.86/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.86/0.99    inference(flattening,[],[f23])).
% 2.86/0.99  
% 2.86/0.99  fof(f38,plain,(
% 2.86/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.86/0.99    introduced(choice_axiom,[])).
% 2.86/0.99  
% 2.86/0.99  fof(f37,plain,(
% 2.86/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 2.86/0.99    introduced(choice_axiom,[])).
% 2.86/0.99  
% 2.86/0.99  fof(f39,plain,(
% 2.86/0.99    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 2.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f24,f38,f37])).
% 2.86/0.99  
% 2.86/0.99  fof(f66,plain,(
% 2.86/0.99    v1_funct_2(sK7,sK4,sK5)),
% 2.86/0.99    inference(cnf_transformation,[],[f39])).
% 2.86/0.99  
% 2.86/0.99  fof(f67,plain,(
% 2.86/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.86/0.99    inference(cnf_transformation,[],[f39])).
% 2.86/0.99  
% 2.86/0.99  fof(f8,axiom,(
% 2.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f19,plain,(
% 2.86/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.99    inference(ennf_transformation,[],[f8])).
% 2.86/0.99  
% 2.86/0.99  fof(f57,plain,(
% 2.86/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/0.99    inference(cnf_transformation,[],[f19])).
% 2.86/0.99  
% 2.86/0.99  fof(f4,axiom,(
% 2.86/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f14,plain,(
% 2.86/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.86/0.99    inference(ennf_transformation,[],[f4])).
% 2.86/0.99  
% 2.86/0.99  fof(f15,plain,(
% 2.86/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/0.99    inference(flattening,[],[f14])).
% 2.86/0.99  
% 2.86/0.99  fof(f30,plain,(
% 2.86/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/0.99    inference(nnf_transformation,[],[f15])).
% 2.86/0.99  
% 2.86/0.99  fof(f31,plain,(
% 2.86/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/0.99    inference(rectify,[],[f30])).
% 2.86/0.99  
% 2.86/0.99  fof(f34,plain,(
% 2.86/0.99    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 2.86/0.99    introduced(choice_axiom,[])).
% 2.86/0.99  
% 2.86/0.99  fof(f33,plain,(
% 2.86/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 2.86/0.99    introduced(choice_axiom,[])).
% 2.86/0.99  
% 2.86/0.99  fof(f32,plain,(
% 2.86/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.86/0.99    introduced(choice_axiom,[])).
% 2.86/0.99  
% 2.86/0.99  fof(f35,plain,(
% 2.86/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).
% 2.86/0.99  
% 2.86/0.99  fof(f47,plain,(
% 2.86/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f35])).
% 2.86/0.99  
% 2.86/0.99  fof(f73,plain,(
% 2.86/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(equality_resolution,[],[f47])).
% 2.86/0.99  
% 2.86/0.99  fof(f65,plain,(
% 2.86/0.99    v1_funct_1(sK7)),
% 2.86/0.99    inference(cnf_transformation,[],[f39])).
% 2.86/0.99  
% 2.86/0.99  fof(f6,axiom,(
% 2.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f17,plain,(
% 2.86/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.99    inference(ennf_transformation,[],[f6])).
% 2.86/0.99  
% 2.86/0.99  fof(f55,plain,(
% 2.86/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/0.99    inference(cnf_transformation,[],[f17])).
% 2.86/0.99  
% 2.86/0.99  fof(f46,plain,(
% 2.86/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f35])).
% 2.86/0.99  
% 2.86/0.99  fof(f74,plain,(
% 2.86/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(equality_resolution,[],[f46])).
% 2.86/0.99  
% 2.86/0.99  fof(f1,axiom,(
% 2.86/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f13,plain,(
% 2.86/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.86/0.99    inference(ennf_transformation,[],[f1])).
% 2.86/0.99  
% 2.86/0.99  fof(f25,plain,(
% 2.86/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.86/0.99    inference(nnf_transformation,[],[f13])).
% 2.86/0.99  
% 2.86/0.99  fof(f26,plain,(
% 2.86/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.86/0.99    inference(rectify,[],[f25])).
% 2.86/0.99  
% 2.86/0.99  fof(f27,plain,(
% 2.86/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.86/0.99    introduced(choice_axiom,[])).
% 2.86/0.99  
% 2.86/0.99  fof(f28,plain,(
% 2.86/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.86/0.99  
% 2.86/0.99  fof(f40,plain,(
% 2.86/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f28])).
% 2.86/0.99  
% 2.86/0.99  fof(f9,axiom,(
% 2.86/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f20,plain,(
% 2.86/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.99    inference(ennf_transformation,[],[f9])).
% 2.86/0.99  
% 2.86/0.99  fof(f58,plain,(
% 2.86/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/0.99    inference(cnf_transformation,[],[f20])).
% 2.86/0.99  
% 2.86/0.99  fof(f68,plain,(
% 2.86/0.99    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 2.86/0.99    inference(cnf_transformation,[],[f39])).
% 2.86/0.99  
% 2.86/0.99  fof(f48,plain,(
% 2.86/0.99    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f35])).
% 2.86/0.99  
% 2.86/0.99  fof(f72,plain,(
% 2.86/0.99    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.86/0.99    inference(equality_resolution,[],[f48])).
% 2.86/0.99  
% 2.86/0.99  fof(f69,plain,(
% 2.86/0.99    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f39])).
% 2.86/0.99  
% 2.86/0.99  fof(f2,axiom,(
% 2.86/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f43,plain,(
% 2.86/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f2])).
% 2.86/0.99  
% 2.86/0.99  fof(f3,axiom,(
% 2.86/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f29,plain,(
% 2.86/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.86/0.99    inference(nnf_transformation,[],[f3])).
% 2.86/0.99  
% 2.86/0.99  fof(f44,plain,(
% 2.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.86/0.99    inference(cnf_transformation,[],[f29])).
% 2.86/0.99  
% 2.86/0.99  fof(f7,axiom,(
% 2.86/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f18,plain,(
% 2.86/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.86/0.99    inference(ennf_transformation,[],[f7])).
% 2.86/0.99  
% 2.86/0.99  fof(f56,plain,(
% 2.86/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.86/0.99    inference(cnf_transformation,[],[f18])).
% 2.86/0.99  
% 2.86/0.99  fof(f5,axiom,(
% 2.86/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.86/0.99  
% 2.86/0.99  fof(f16,plain,(
% 2.86/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.86/0.99    inference(ennf_transformation,[],[f5])).
% 2.86/0.99  
% 2.86/0.99  fof(f54,plain,(
% 2.86/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f16])).
% 2.86/0.99  
% 2.86/0.99  fof(f41,plain,(
% 2.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f28])).
% 2.86/0.99  
% 2.86/0.99  fof(f42,plain,(
% 2.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.86/0.99    inference(cnf_transformation,[],[f28])).
% 2.86/0.99  
% 2.86/0.99  cnf(c_24,plain,
% 2.86/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.86/0.99      | k1_xboole_0 = X2 ),
% 2.86/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_28,negated_conjecture,
% 2.86/0.99      ( v1_funct_2(sK7,sK4,sK5) ),
% 2.86/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_943,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.86/0.99      | sK5 != X2
% 2.86/0.99      | sK4 != X1
% 2.86/0.99      | sK7 != X0
% 2.86/0.99      | k1_xboole_0 = X2 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_944,plain,
% 2.86/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.86/0.99      | k1_relset_1(sK4,sK5,sK7) = sK4
% 2.86/0.99      | k1_xboole_0 = sK5 ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_943]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_27,negated_conjecture,
% 2.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.86/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_946,plain,
% 2.86/0.99      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 2.86/0.99      inference(global_propositional_subsumption,[status(thm)],[c_944,c_27]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2075,plain,
% 2.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_17,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2079,plain,
% 2.86/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3191,plain,
% 2.86/0.99      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2075,c_2079]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3295,plain,
% 2.86/0.99      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_946,c_3191]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_12,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.86/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 2.86/0.99      | ~ v1_relat_1(X1)
% 2.86/0.99      | ~ v1_funct_1(X1) ),
% 2.86/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_29,negated_conjecture,
% 2.86/0.99      ( v1_funct_1(sK7) ),
% 2.86/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_661,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.86/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 2.86/0.99      | ~ v1_relat_1(X1)
% 2.86/0.99      | sK7 != X1 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_662,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 2.86/0.99      | r2_hidden(sK3(sK7,X1,X0),X1)
% 2.86/0.99      | ~ v1_relat_1(sK7) ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_661]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2068,plain,
% 2.86/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.86/0.99      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 2.86/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_32,plain,
% 2.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_663,plain,
% 2.86/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.86/0.99      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 2.86/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_15,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2287,plain,
% 2.86/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.86/0.99      | v1_relat_1(sK7) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2288,plain,
% 2.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.86/0.99      | v1_relat_1(sK7) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2287]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2344,plain,
% 2.86/0.99      ( r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 2.86/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_2068,c_32,c_663,c_2288]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2345,plain,
% 2.86/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.86/0.99      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top ),
% 2.86/0.99      inference(renaming,[status(thm)],[c_2344]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_13,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.86/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 2.86/0.99      | ~ v1_relat_1(X1)
% 2.86/0.99      | ~ v1_funct_1(X1) ),
% 2.86/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_646,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.86/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 2.86/0.99      | ~ v1_relat_1(X1)
% 2.86/0.99      | sK7 != X1 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_647,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 2.86/0.99      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7))
% 2.86/0.99      | ~ v1_relat_1(sK7) ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_646]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2069,plain,
% 2.86/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.86/0.99      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
% 2.86/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_648,plain,
% 2.86/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.86/0.99      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
% 2.86/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2357,plain,
% 2.86/0.99      ( r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
% 2.86/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_2069,c_32,c_648,c_2288]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2358,plain,
% 2.86/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.86/0.99      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top ),
% 2.86/0.99      inference(renaming,[status(thm)],[c_2357]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.86/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2086,plain,
% 2.86/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.86/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.86/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3959,plain,
% 2.86/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.86/0.99      | r2_hidden(sK3(sK7,X1,X0),X2) = iProver_top
% 2.86/0.99      | r1_tarski(k1_relat_1(sK7),X2) != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2358,c_2086]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_18,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.86/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2078,plain,
% 2.86/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2996,plain,
% 2.86/0.99      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2075,c_2078]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_26,negated_conjecture,
% 2.86/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 2.86/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2076,plain,
% 2.86/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3460,plain,
% 2.86/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 2.86/0.99      inference(demodulation,[status(thm)],[c_2996,c_2076]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_11,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.86/0.99      | ~ v1_relat_1(X1)
% 2.86/0.99      | ~ v1_funct_1(X1)
% 2.86/0.99      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 2.86/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_676,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.86/0.99      | ~ v1_relat_1(X1)
% 2.86/0.99      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
% 2.86/0.99      | sK7 != X1 ),
% 2.86/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_677,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 2.86/0.99      | ~ v1_relat_1(sK7)
% 2.86/0.99      | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
% 2.86/0.99      inference(unflattening,[status(thm)],[c_676]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2067,plain,
% 2.86/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
% 2.86/0.99      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 2.86/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_678,plain,
% 2.86/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
% 2.86/0.99      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 2.86/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2312,plain,
% 2.86/0.99      ( r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 2.86/0.99      | k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1 ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_2067,c_32,c_678,c_2288]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2313,plain,
% 2.86/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
% 2.86/0.99      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
% 2.86/0.99      inference(renaming,[status(thm)],[c_2312]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3470,plain,
% 2.86/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3460,c_2313]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_25,negated_conjecture,
% 2.86/0.99      ( ~ r2_hidden(X0,sK4) | ~ r2_hidden(X0,sK6) | k1_funct_1(sK7,X0) != sK8 ),
% 2.86/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2077,plain,
% 2.86/0.99      ( k1_funct_1(sK7,X0) != sK8
% 2.86/0.99      | r2_hidden(X0,sK4) != iProver_top
% 2.86/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3645,plain,
% 2.86/0.99      ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
% 2.86/0.99      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3470,c_2077]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6076,plain,
% 2.86/0.99      ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 2.86/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 2.86/0.99      | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3959,c_3645]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6810,plain,
% 2.86/0.99      ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 2.86/0.99      | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6076,c_3460]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6816,plain,
% 2.86/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 2.86/0.99      | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2345,c_6810]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6876,plain,
% 2.86/0.99      ( r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6816,c_3460]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6881,plain,
% 2.86/0.99      ( sK5 = k1_xboole_0 | r1_tarski(sK4,sK4) != iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_3295,c_6876]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3,plain,
% 2.86/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2577,plain,
% 2.86/0.99      ( r1_tarski(k1_xboole_0,sK8) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.86/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2387,plain,
% 2.86/0.99      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
% 2.86/0.99      | r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),X0) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2969,plain,
% 2.86/0.99      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 2.86/0.99      | r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),sK5) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_2387]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_16,plain,
% 2.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.86/0.99      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 2.86/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2321,plain,
% 2.86/0.99      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
% 2.86/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2970,plain,
% 2.86/0.99      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 2.86/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_2321]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2296,plain,
% 2.86/0.99      ( r2_hidden(sK8,X0)
% 2.86/0.99      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 2.86/0.99      | ~ r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),X0) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3287,plain,
% 2.86/0.99      ( ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 2.86/0.99      | r2_hidden(sK8,sK5)
% 2.86/0.99      | ~ r1_tarski(k7_relset_1(sK4,sK5,sK7,sK6),sK5) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_2296]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_14,plain,
% 2.86/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.86/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2589,plain,
% 2.86/0.99      ( ~ r2_hidden(sK8,X0) | ~ r1_tarski(X0,sK8) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_4396,plain,
% 2.86/0.99      ( ~ r2_hidden(sK8,sK5) | ~ r1_tarski(sK5,sK8) ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_2589]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1474,plain,
% 2.86/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.86/0.99      theory(equality) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2582,plain,
% 2.86/0.99      ( ~ r1_tarski(X0,sK8) | r1_tarski(X1,sK8) | X1 != X0 ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_1474]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5182,plain,
% 2.86/0.99      ( ~ r1_tarski(X0,sK8) | r1_tarski(sK5,sK8) | sK5 != X0 ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_2582]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_5184,plain,
% 2.86/0.99      ( r1_tarski(sK5,sK8)
% 2.86/0.99      | ~ r1_tarski(k1_xboole_0,sK8)
% 2.86/0.99      | sK5 != k1_xboole_0 ),
% 2.86/0.99      inference(instantiation,[status(thm)],[c_5182]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6884,plain,
% 2.86/0.99      ( r1_tarski(sK4,sK4) != iProver_top ),
% 2.86/0.99      inference(global_propositional_subsumption,
% 2.86/0.99                [status(thm)],
% 2.86/0.99                [c_6881,c_27,c_26,c_2577,c_2969,c_2970,c_3287,c_4396,c_5184]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_1,plain,
% 2.86/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.86/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2087,plain,
% 2.86/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.86/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_0,plain,
% 2.86/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.86/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_2088,plain,
% 2.86/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.86/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.86/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_3185,plain,
% 2.86/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.86/0.99      inference(superposition,[status(thm)],[c_2087,c_2088]) ).
% 2.86/0.99  
% 2.86/0.99  cnf(c_6889,plain,
% 2.86/0.99      ( $false ),
% 2.86/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_6884,c_3185]) ).
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.86/0.99  
% 2.86/0.99  ------                               Statistics
% 2.86/0.99  
% 2.86/0.99  ------ General
% 2.86/0.99  
% 2.86/0.99  abstr_ref_over_cycles:                  0
% 2.86/0.99  abstr_ref_under_cycles:                 0
% 2.86/0.99  gc_basic_clause_elim:                   0
% 2.86/0.99  forced_gc_time:                         0
% 2.86/0.99  parsing_time:                           0.008
% 2.86/0.99  unif_index_cands_time:                  0.
% 2.86/0.99  unif_index_add_time:                    0.
% 2.86/0.99  orderings_time:                         0.
% 2.86/0.99  out_proof_time:                         0.011
% 2.86/0.99  total_time:                             0.238
% 2.86/0.99  num_of_symbols:                         54
% 2.86/0.99  num_of_terms:                           6542
% 2.86/0.99  
% 2.86/0.99  ------ Preprocessing
% 2.86/0.99  
% 2.86/0.99  num_of_splits:                          0
% 2.86/0.99  num_of_split_atoms:                     0
% 2.86/0.99  num_of_reused_defs:                     0
% 2.86/0.99  num_eq_ax_congr_red:                    38
% 2.86/0.99  num_of_sem_filtered_clauses:            1
% 2.86/0.99  num_of_subtypes:                        0
% 2.86/0.99  monotx_restored_types:                  0
% 2.86/0.99  sat_num_of_epr_types:                   0
% 2.86/0.99  sat_num_of_non_cyclic_types:            0
% 2.86/0.99  sat_guarded_non_collapsed_types:        0
% 2.86/0.99  num_pure_diseq_elim:                    0
% 2.86/0.99  simp_replaced_by:                       0
% 2.86/0.99  res_preprocessed:                       138
% 2.86/0.99  prep_upred:                             0
% 2.86/0.99  prep_unflattend:                        87
% 2.86/0.99  smt_new_axioms:                         0
% 2.86/0.99  pred_elim_cands:                        4
% 2.86/0.99  pred_elim:                              2
% 2.86/0.99  pred_elim_cl:                           5
% 2.86/0.99  pred_elim_cycles:                       7
% 2.86/0.99  merged_defs:                            8
% 2.86/0.99  merged_defs_ncl:                        0
% 2.86/0.99  bin_hyper_res:                          8
% 2.86/0.99  prep_cycles:                            4
% 2.86/0.99  pred_elim_time:                         0.014
% 2.86/0.99  splitting_time:                         0.
% 2.86/0.99  sem_filter_time:                        0.
% 2.86/0.99  monotx_time:                            0.
% 2.86/0.99  subtype_inf_time:                       0.
% 2.86/0.99  
% 2.86/0.99  ------ Problem properties
% 2.86/0.99  
% 2.86/0.99  clauses:                                25
% 2.86/0.99  conjectures:                            3
% 2.86/0.99  epr:                                    3
% 2.86/0.99  horn:                                   19
% 2.86/0.99  ground:                                 5
% 2.86/0.99  unary:                                  3
% 2.86/0.99  binary:                                 10
% 2.86/0.99  lits:                                   67
% 2.86/0.99  lits_eq:                                17
% 2.86/0.99  fd_pure:                                0
% 2.86/0.99  fd_pseudo:                              0
% 2.86/0.99  fd_cond:                                0
% 2.86/0.99  fd_pseudo_cond:                         4
% 2.86/0.99  ac_symbols:                             0
% 2.86/0.99  
% 2.86/0.99  ------ Propositional Solver
% 2.86/0.99  
% 2.86/0.99  prop_solver_calls:                      28
% 2.86/0.99  prop_fast_solver_calls:                 1086
% 2.86/0.99  smt_solver_calls:                       0
% 2.86/0.99  smt_fast_solver_calls:                  0
% 2.86/0.99  prop_num_of_clauses:                    2433
% 2.86/0.99  prop_preprocess_simplified:             6464
% 2.86/0.99  prop_fo_subsumed:                       18
% 2.86/0.99  prop_solver_time:                       0.
% 2.86/0.99  smt_solver_time:                        0.
% 2.86/0.99  smt_fast_solver_time:                   0.
% 2.86/0.99  prop_fast_solver_time:                  0.
% 2.86/0.99  prop_unsat_core_time:                   0.
% 2.86/0.99  
% 2.86/0.99  ------ QBF
% 2.86/0.99  
% 2.86/0.99  qbf_q_res:                              0
% 2.86/0.99  qbf_num_tautologies:                    0
% 2.86/0.99  qbf_prep_cycles:                        0
% 2.86/0.99  
% 2.86/0.99  ------ BMC1
% 2.86/0.99  
% 2.86/0.99  bmc1_current_bound:                     -1
% 2.86/0.99  bmc1_last_solved_bound:                 -1
% 2.86/0.99  bmc1_unsat_core_size:                   -1
% 2.86/0.99  bmc1_unsat_core_parents_size:           -1
% 2.86/0.99  bmc1_merge_next_fun:                    0
% 2.86/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.86/0.99  
% 2.86/0.99  ------ Instantiation
% 2.86/0.99  
% 2.86/0.99  inst_num_of_clauses:                    568
% 2.86/0.99  inst_num_in_passive:                    61
% 2.86/0.99  inst_num_in_active:                     283
% 2.86/0.99  inst_num_in_unprocessed:                224
% 2.86/0.99  inst_num_of_loops:                      350
% 2.86/0.99  inst_num_of_learning_restarts:          0
% 2.86/0.99  inst_num_moves_active_passive:          64
% 2.86/0.99  inst_lit_activity:                      0
% 2.86/0.99  inst_lit_activity_moves:                0
% 2.86/0.99  inst_num_tautologies:                   0
% 2.86/0.99  inst_num_prop_implied:                  0
% 2.86/0.99  inst_num_existing_simplified:           0
% 2.86/0.99  inst_num_eq_res_simplified:             0
% 2.86/0.99  inst_num_child_elim:                    0
% 2.86/0.99  inst_num_of_dismatching_blockings:      129
% 2.86/0.99  inst_num_of_non_proper_insts:           434
% 2.86/0.99  inst_num_of_duplicates:                 0
% 2.86/0.99  inst_inst_num_from_inst_to_res:         0
% 2.86/0.99  inst_dismatching_checking_time:         0.
% 2.86/0.99  
% 2.86/0.99  ------ Resolution
% 2.86/0.99  
% 2.86/0.99  res_num_of_clauses:                     0
% 2.86/0.99  res_num_in_passive:                     0
% 2.86/0.99  res_num_in_active:                      0
% 2.86/0.99  res_num_of_loops:                       142
% 2.86/0.99  res_forward_subset_subsumed:            19
% 2.86/0.99  res_backward_subset_subsumed:           2
% 2.86/0.99  res_forward_subsumed:                   0
% 2.86/0.99  res_backward_subsumed:                  1
% 2.86/0.99  res_forward_subsumption_resolution:     0
% 2.86/0.99  res_backward_subsumption_resolution:    1
% 2.86/0.99  res_clause_to_clause_subsumption:       541
% 2.86/0.99  res_orphan_elimination:                 0
% 2.86/0.99  res_tautology_del:                      69
% 2.86/0.99  res_num_eq_res_simplified:              0
% 2.86/0.99  res_num_sel_changes:                    0
% 2.86/0.99  res_moves_from_active_to_pass:          0
% 2.86/0.99  
% 2.86/0.99  ------ Superposition
% 2.86/0.99  
% 2.86/0.99  sup_time_total:                         0.
% 2.86/0.99  sup_time_generating:                    0.
% 2.86/0.99  sup_time_sim_full:                      0.
% 2.86/0.99  sup_time_sim_immed:                     0.
% 2.86/0.99  
% 2.86/0.99  sup_num_of_clauses:                     197
% 2.86/0.99  sup_num_in_active:                      67
% 2.86/0.99  sup_num_in_passive:                     130
% 2.86/0.99  sup_num_of_loops:                       69
% 2.86/0.99  sup_fw_superposition:                   145
% 2.86/0.99  sup_bw_superposition:                   64
% 2.86/0.99  sup_immediate_simplified:               17
% 2.86/0.99  sup_given_eliminated:                   0
% 2.86/0.99  comparisons_done:                       0
% 2.86/0.99  comparisons_avoided:                    5
% 2.86/0.99  
% 2.86/0.99  ------ Simplifications
% 2.86/0.99  
% 2.86/0.99  
% 2.86/0.99  sim_fw_subset_subsumed:                 9
% 2.86/0.99  sim_bw_subset_subsumed:                 5
% 2.86/0.99  sim_fw_subsumed:                        0
% 2.86/0.99  sim_bw_subsumed:                        3
% 2.86/0.99  sim_fw_subsumption_res:                 1
% 2.86/0.99  sim_bw_subsumption_res:                 0
% 2.86/0.99  sim_tautology_del:                      1
% 2.86/0.99  sim_eq_tautology_del:                   0
% 2.86/0.99  sim_eq_res_simp:                        0
% 2.86/0.99  sim_fw_demodulated:                     0
% 2.86/0.99  sim_bw_demodulated:                     2
% 2.86/0.99  sim_light_normalised:                   0
% 2.86/0.99  sim_joinable_taut:                      0
% 2.86/0.99  sim_joinable_simp:                      0
% 2.86/0.99  sim_ac_normalised:                      0
% 2.86/0.99  sim_smt_subsumption:                    0
% 2.86/0.99  
%------------------------------------------------------------------------------

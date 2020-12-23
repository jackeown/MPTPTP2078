%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:13 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 266 expanded)
%              Number of clauses        :   62 (  84 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  467 (1457 expanded)
%              Number of equality atoms :  172 ( 418 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f41,plain,(
    ! [X4,X2,X0,X3] :
      ( ? [X5] :
          ( k1_funct_1(X3,X5) = X4
          & r2_hidden(X5,X2)
          & r2_hidden(X5,X0) )
     => ( k1_funct_1(X3,sK11) = X4
        & r2_hidden(sK11,X2)
        & r2_hidden(sK11,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
     => ( ~ r2_hidden(sK10,k7_relset_1(X0,X1,X3,X2))
        & ? [X5] :
            ( k1_funct_1(X3,X5) = sK10
            & r2_hidden(X5,X2)
            & r2_hidden(X5,X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
          ( ~ r2_hidden(X4,k7_relset_1(sK6,sK7,sK9,sK8))
          & ? [X5] :
              ( k1_funct_1(sK9,X5) = X4
              & r2_hidden(X5,sK8)
              & r2_hidden(X5,sK6) ) )
      & k1_xboole_0 != sK7
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK9,sK6,sK7)
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))
    & k1_funct_1(sK9,sK11) = sK10
    & r2_hidden(sK11,sK8)
    & r2_hidden(sK11,sK6)
    & k1_xboole_0 != sK7
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK9,sK6,sK7)
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f20,f41,f40,f39])).

fof(f72,plain,(
    k1_funct_1(sK9,sK11) = sK10 ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

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
    inference(nnf_transformation,[],[f14])).

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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f66,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    r2_hidden(sK11,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f16])).

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
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK5(X1,X2),X6),X2)
        & r2_hidden(sK5(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK5(X1,X2),X6),X2)
            & r2_hidden(sK5(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f36,f35])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f12])).

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
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ~ r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    r2_hidden(sK11,sK8) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_24,negated_conjecture,
    ( k1_funct_1(sK9,sK11) = sK10 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_325,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1084,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_326,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_769,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1272,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_362,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_363,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK9)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_1267,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK9)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_1395,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK6,sK7))
    | v1_relat_1(sK9)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_1396,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | v1_relat_1(k2_zfmisc_1(sK6,sK7)) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1395])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1511,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1512,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1511])).

cnf(c_1750,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1084,c_326,c_1272,c_1396,c_1512])).

cnf(c_1751,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_1750])).

cnf(c_1758,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK9) = iProver_top
    | r2_hidden(sK11,k1_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1751])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK11,sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,plain,
    ( r2_hidden(sK11,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_377,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK9 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_378,plain,
    ( ~ v1_funct_2(sK9,X0,X1)
    | k1_relset_1(X0,X1,sK9) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_590,plain,
    ( k1_relset_1(X0,X1,sK9) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK9 != sK9
    | sK7 != X1
    | sK6 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_378])).

cnf(c_591,plain,
    ( k1_relset_1(sK6,sK7,sK9) = sK6
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = sK7 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_592,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_relset_1(sK6,sK7,sK9) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_27])).

cnf(c_593,plain,
    ( k1_relset_1(sK6,sK7,sK9) = sK6
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_592])).

cnf(c_660,plain,
    ( k1_relset_1(sK6,sK7,sK9) = sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_593])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1329,plain,
    ( ~ r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9)
    | r2_hidden(sK11,k1_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1330,plain,
    ( r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9) != iProver_top
    | r2_hidden(sK11,k1_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK4(X2,X0)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | k1_relset_1(X1,X3,X2) != X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_422,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK4(X2,X0)),X2)
    | k1_relset_1(X1,X3,X2) != X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK9 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_423,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK4(sK9,X0)),sK9)
    | k1_relset_1(X1,X2,sK9) != X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_1262,plain,
    ( r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9)
    | ~ r2_hidden(sK11,sK6)
    | k1_relset_1(sK6,X0,sK9) != sK6
    | k1_zfmisc_1(k2_zfmisc_1(sK6,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_1449,plain,
    ( r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9)
    | ~ r2_hidden(sK11,sK6)
    | k1_relset_1(sK6,sK7,sK9) != sK6
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_1450,plain,
    ( k1_relset_1(sK6,sK7,sK9) != sK6
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9) = iProver_top
    | r2_hidden(sK11,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_1872,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1758,c_34,c_660,c_1272,c_1330,c_1450])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1091,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1094,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1210,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1091,c_1094])).

cnf(c_2633,plain,
    ( r2_hidden(sK11,X0) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_1210])).

cnf(c_3240,plain,
    ( r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top
    | r2_hidden(sK11,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2633,c_1272,c_1396,c_1512])).

cnf(c_3241,plain,
    ( r2_hidden(sK11,X0) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3240])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_413,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK9 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_414,plain,
    ( k7_relset_1(X0,X1,sK9,X2) = k9_relat_1(sK9,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_1317,plain,
    ( k7_relset_1(sK6,sK7,sK9,X0) = k9_relat_1(sK9,X0) ),
    inference(equality_resolution,[status(thm)],[c_414])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1087,plain,
    ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1522,plain,
    ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1317,c_1087])).

cnf(c_3248,plain,
    ( r2_hidden(sK11,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3241,c_1522])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK11,sK8) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( r2_hidden(sK11,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3248,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.48/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.02  
% 2.48/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/1.02  
% 2.48/1.02  ------  iProver source info
% 2.48/1.02  
% 2.48/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.48/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/1.02  git: non_committed_changes: false
% 2.48/1.02  git: last_make_outside_of_git: false
% 2.48/1.02  
% 2.48/1.02  ------ 
% 2.48/1.02  
% 2.48/1.02  ------ Input Options
% 2.48/1.02  
% 2.48/1.02  --out_options                           all
% 2.48/1.02  --tptp_safe_out                         true
% 2.48/1.02  --problem_path                          ""
% 2.48/1.02  --include_path                          ""
% 2.48/1.02  --clausifier                            res/vclausify_rel
% 2.48/1.02  --clausifier_options                    --mode clausify
% 2.48/1.02  --stdin                                 false
% 2.48/1.02  --stats_out                             all
% 2.48/1.02  
% 2.48/1.02  ------ General Options
% 2.48/1.02  
% 2.48/1.02  --fof                                   false
% 2.48/1.02  --time_out_real                         305.
% 2.48/1.02  --time_out_virtual                      -1.
% 2.48/1.02  --symbol_type_check                     false
% 2.48/1.02  --clausify_out                          false
% 2.48/1.02  --sig_cnt_out                           false
% 2.48/1.02  --trig_cnt_out                          false
% 2.48/1.02  --trig_cnt_out_tolerance                1.
% 2.48/1.02  --trig_cnt_out_sk_spl                   false
% 2.48/1.02  --abstr_cl_out                          false
% 2.48/1.02  
% 2.48/1.02  ------ Global Options
% 2.48/1.02  
% 2.48/1.02  --schedule                              default
% 2.48/1.02  --add_important_lit                     false
% 2.48/1.02  --prop_solver_per_cl                    1000
% 2.48/1.02  --min_unsat_core                        false
% 2.48/1.02  --soft_assumptions                      false
% 2.48/1.02  --soft_lemma_size                       3
% 2.48/1.02  --prop_impl_unit_size                   0
% 2.48/1.02  --prop_impl_unit                        []
% 2.48/1.02  --share_sel_clauses                     true
% 2.48/1.02  --reset_solvers                         false
% 2.48/1.02  --bc_imp_inh                            [conj_cone]
% 2.48/1.02  --conj_cone_tolerance                   3.
% 2.48/1.02  --extra_neg_conj                        none
% 2.48/1.02  --large_theory_mode                     true
% 2.48/1.02  --prolific_symb_bound                   200
% 2.48/1.02  --lt_threshold                          2000
% 2.48/1.02  --clause_weak_htbl                      true
% 2.48/1.02  --gc_record_bc_elim                     false
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing Options
% 2.48/1.02  
% 2.48/1.02  --preprocessing_flag                    true
% 2.48/1.02  --time_out_prep_mult                    0.1
% 2.48/1.02  --splitting_mode                        input
% 2.48/1.02  --splitting_grd                         true
% 2.48/1.02  --splitting_cvd                         false
% 2.48/1.02  --splitting_cvd_svl                     false
% 2.48/1.02  --splitting_nvd                         32
% 2.48/1.02  --sub_typing                            true
% 2.48/1.02  --prep_gs_sim                           true
% 2.48/1.02  --prep_unflatten                        true
% 2.48/1.02  --prep_res_sim                          true
% 2.48/1.02  --prep_upred                            true
% 2.48/1.02  --prep_sem_filter                       exhaustive
% 2.48/1.02  --prep_sem_filter_out                   false
% 2.48/1.02  --pred_elim                             true
% 2.48/1.02  --res_sim_input                         true
% 2.48/1.02  --eq_ax_congr_red                       true
% 2.48/1.02  --pure_diseq_elim                       true
% 2.48/1.02  --brand_transform                       false
% 2.48/1.02  --non_eq_to_eq                          false
% 2.48/1.02  --prep_def_merge                        true
% 2.48/1.02  --prep_def_merge_prop_impl              false
% 2.48/1.02  --prep_def_merge_mbd                    true
% 2.48/1.02  --prep_def_merge_tr_red                 false
% 2.48/1.02  --prep_def_merge_tr_cl                  false
% 2.48/1.02  --smt_preprocessing                     true
% 2.48/1.02  --smt_ac_axioms                         fast
% 2.48/1.02  --preprocessed_out                      false
% 2.48/1.02  --preprocessed_stats                    false
% 2.48/1.02  
% 2.48/1.02  ------ Abstraction refinement Options
% 2.48/1.02  
% 2.48/1.02  --abstr_ref                             []
% 2.48/1.02  --abstr_ref_prep                        false
% 2.48/1.02  --abstr_ref_until_sat                   false
% 2.48/1.02  --abstr_ref_sig_restrict                funpre
% 2.48/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.02  --abstr_ref_under                       []
% 2.48/1.02  
% 2.48/1.02  ------ SAT Options
% 2.48/1.02  
% 2.48/1.02  --sat_mode                              false
% 2.48/1.02  --sat_fm_restart_options                ""
% 2.48/1.02  --sat_gr_def                            false
% 2.48/1.02  --sat_epr_types                         true
% 2.48/1.02  --sat_non_cyclic_types                  false
% 2.48/1.02  --sat_finite_models                     false
% 2.48/1.02  --sat_fm_lemmas                         false
% 2.48/1.02  --sat_fm_prep                           false
% 2.48/1.02  --sat_fm_uc_incr                        true
% 2.48/1.02  --sat_out_model                         small
% 2.48/1.02  --sat_out_clauses                       false
% 2.48/1.02  
% 2.48/1.02  ------ QBF Options
% 2.48/1.02  
% 2.48/1.02  --qbf_mode                              false
% 2.48/1.02  --qbf_elim_univ                         false
% 2.48/1.02  --qbf_dom_inst                          none
% 2.48/1.02  --qbf_dom_pre_inst                      false
% 2.48/1.02  --qbf_sk_in                             false
% 2.48/1.02  --qbf_pred_elim                         true
% 2.48/1.02  --qbf_split                             512
% 2.48/1.02  
% 2.48/1.02  ------ BMC1 Options
% 2.48/1.02  
% 2.48/1.02  --bmc1_incremental                      false
% 2.48/1.02  --bmc1_axioms                           reachable_all
% 2.48/1.02  --bmc1_min_bound                        0
% 2.48/1.02  --bmc1_max_bound                        -1
% 2.48/1.02  --bmc1_max_bound_default                -1
% 2.48/1.02  --bmc1_symbol_reachability              true
% 2.48/1.02  --bmc1_property_lemmas                  false
% 2.48/1.02  --bmc1_k_induction                      false
% 2.48/1.02  --bmc1_non_equiv_states                 false
% 2.48/1.02  --bmc1_deadlock                         false
% 2.48/1.02  --bmc1_ucm                              false
% 2.48/1.02  --bmc1_add_unsat_core                   none
% 2.48/1.02  --bmc1_unsat_core_children              false
% 2.48/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.02  --bmc1_out_stat                         full
% 2.48/1.02  --bmc1_ground_init                      false
% 2.48/1.02  --bmc1_pre_inst_next_state              false
% 2.48/1.02  --bmc1_pre_inst_state                   false
% 2.48/1.02  --bmc1_pre_inst_reach_state             false
% 2.48/1.02  --bmc1_out_unsat_core                   false
% 2.48/1.02  --bmc1_aig_witness_out                  false
% 2.48/1.02  --bmc1_verbose                          false
% 2.48/1.02  --bmc1_dump_clauses_tptp                false
% 2.48/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.02  --bmc1_dump_file                        -
% 2.48/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.02  --bmc1_ucm_extend_mode                  1
% 2.48/1.02  --bmc1_ucm_init_mode                    2
% 2.48/1.02  --bmc1_ucm_cone_mode                    none
% 2.48/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.02  --bmc1_ucm_relax_model                  4
% 2.48/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.02  --bmc1_ucm_layered_model                none
% 2.48/1.02  --bmc1_ucm_max_lemma_size               10
% 2.48/1.02  
% 2.48/1.02  ------ AIG Options
% 2.48/1.02  
% 2.48/1.02  --aig_mode                              false
% 2.48/1.02  
% 2.48/1.02  ------ Instantiation Options
% 2.48/1.02  
% 2.48/1.02  --instantiation_flag                    true
% 2.48/1.02  --inst_sos_flag                         false
% 2.48/1.02  --inst_sos_phase                        true
% 2.48/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel_side                     num_symb
% 2.48/1.02  --inst_solver_per_active                1400
% 2.48/1.02  --inst_solver_calls_frac                1.
% 2.48/1.02  --inst_passive_queue_type               priority_queues
% 2.48/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.02  --inst_passive_queues_freq              [25;2]
% 2.48/1.02  --inst_dismatching                      true
% 2.48/1.02  --inst_eager_unprocessed_to_passive     true
% 2.48/1.02  --inst_prop_sim_given                   true
% 2.48/1.02  --inst_prop_sim_new                     false
% 2.48/1.02  --inst_subs_new                         false
% 2.48/1.02  --inst_eq_res_simp                      false
% 2.48/1.02  --inst_subs_given                       false
% 2.48/1.02  --inst_orphan_elimination               true
% 2.48/1.02  --inst_learning_loop_flag               true
% 2.48/1.02  --inst_learning_start                   3000
% 2.48/1.02  --inst_learning_factor                  2
% 2.48/1.02  --inst_start_prop_sim_after_learn       3
% 2.48/1.02  --inst_sel_renew                        solver
% 2.48/1.02  --inst_lit_activity_flag                true
% 2.48/1.02  --inst_restr_to_given                   false
% 2.48/1.02  --inst_activity_threshold               500
% 2.48/1.02  --inst_out_proof                        true
% 2.48/1.02  
% 2.48/1.02  ------ Resolution Options
% 2.48/1.02  
% 2.48/1.02  --resolution_flag                       true
% 2.48/1.02  --res_lit_sel                           adaptive
% 2.48/1.02  --res_lit_sel_side                      none
% 2.48/1.02  --res_ordering                          kbo
% 2.48/1.02  --res_to_prop_solver                    active
% 2.48/1.02  --res_prop_simpl_new                    false
% 2.48/1.02  --res_prop_simpl_given                  true
% 2.48/1.02  --res_passive_queue_type                priority_queues
% 2.48/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.02  --res_passive_queues_freq               [15;5]
% 2.48/1.02  --res_forward_subs                      full
% 2.48/1.02  --res_backward_subs                     full
% 2.48/1.02  --res_forward_subs_resolution           true
% 2.48/1.02  --res_backward_subs_resolution          true
% 2.48/1.02  --res_orphan_elimination                true
% 2.48/1.02  --res_time_limit                        2.
% 2.48/1.02  --res_out_proof                         true
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Options
% 2.48/1.02  
% 2.48/1.02  --superposition_flag                    true
% 2.48/1.02  --sup_passive_queue_type                priority_queues
% 2.48/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.02  --demod_completeness_check              fast
% 2.48/1.02  --demod_use_ground                      true
% 2.48/1.02  --sup_to_prop_solver                    passive
% 2.48/1.02  --sup_prop_simpl_new                    true
% 2.48/1.02  --sup_prop_simpl_given                  true
% 2.48/1.02  --sup_fun_splitting                     false
% 2.48/1.02  --sup_smt_interval                      50000
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Simplification Setup
% 2.48/1.02  
% 2.48/1.02  --sup_indices_passive                   []
% 2.48/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.02  --sup_full_bw                           [BwDemod]
% 2.48/1.02  --sup_immed_triv                        [TrivRules]
% 2.48/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.02  --sup_immed_bw_main                     []
% 2.48/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.02  
% 2.48/1.02  ------ Combination Options
% 2.48/1.02  
% 2.48/1.02  --comb_res_mult                         3
% 2.48/1.02  --comb_sup_mult                         2
% 2.48/1.02  --comb_inst_mult                        10
% 2.48/1.02  
% 2.48/1.02  ------ Debug Options
% 2.48/1.02  
% 2.48/1.02  --dbg_backtrace                         false
% 2.48/1.02  --dbg_dump_prop_clauses                 false
% 2.48/1.02  --dbg_dump_prop_clauses_file            -
% 2.48/1.02  --dbg_out_stat                          false
% 2.48/1.02  ------ Parsing...
% 2.48/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.48/1.02  ------ Proving...
% 2.48/1.02  ------ Problem Properties 
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  clauses                                 24
% 2.48/1.02  conjectures                             5
% 2.48/1.02  EPR                                     3
% 2.48/1.02  Horn                                    21
% 2.48/1.02  unary                                   7
% 2.48/1.02  binary                                  3
% 2.48/1.02  lits                                    59
% 2.48/1.02  lits eq                                 22
% 2.48/1.02  fd_pure                                 0
% 2.48/1.02  fd_pseudo                               0
% 2.48/1.02  fd_cond                                 0
% 2.48/1.02  fd_pseudo_cond                          3
% 2.48/1.02  AC symbols                              0
% 2.48/1.02  
% 2.48/1.02  ------ Schedule dynamic 5 is on 
% 2.48/1.02  
% 2.48/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  ------ 
% 2.48/1.02  Current options:
% 2.48/1.02  ------ 
% 2.48/1.02  
% 2.48/1.02  ------ Input Options
% 2.48/1.02  
% 2.48/1.02  --out_options                           all
% 2.48/1.02  --tptp_safe_out                         true
% 2.48/1.02  --problem_path                          ""
% 2.48/1.02  --include_path                          ""
% 2.48/1.02  --clausifier                            res/vclausify_rel
% 2.48/1.02  --clausifier_options                    --mode clausify
% 2.48/1.02  --stdin                                 false
% 2.48/1.02  --stats_out                             all
% 2.48/1.02  
% 2.48/1.02  ------ General Options
% 2.48/1.02  
% 2.48/1.02  --fof                                   false
% 2.48/1.02  --time_out_real                         305.
% 2.48/1.02  --time_out_virtual                      -1.
% 2.48/1.02  --symbol_type_check                     false
% 2.48/1.02  --clausify_out                          false
% 2.48/1.02  --sig_cnt_out                           false
% 2.48/1.02  --trig_cnt_out                          false
% 2.48/1.02  --trig_cnt_out_tolerance                1.
% 2.48/1.02  --trig_cnt_out_sk_spl                   false
% 2.48/1.02  --abstr_cl_out                          false
% 2.48/1.02  
% 2.48/1.02  ------ Global Options
% 2.48/1.02  
% 2.48/1.02  --schedule                              default
% 2.48/1.02  --add_important_lit                     false
% 2.48/1.02  --prop_solver_per_cl                    1000
% 2.48/1.02  --min_unsat_core                        false
% 2.48/1.02  --soft_assumptions                      false
% 2.48/1.02  --soft_lemma_size                       3
% 2.48/1.02  --prop_impl_unit_size                   0
% 2.48/1.02  --prop_impl_unit                        []
% 2.48/1.02  --share_sel_clauses                     true
% 2.48/1.02  --reset_solvers                         false
% 2.48/1.02  --bc_imp_inh                            [conj_cone]
% 2.48/1.02  --conj_cone_tolerance                   3.
% 2.48/1.02  --extra_neg_conj                        none
% 2.48/1.02  --large_theory_mode                     true
% 2.48/1.02  --prolific_symb_bound                   200
% 2.48/1.02  --lt_threshold                          2000
% 2.48/1.02  --clause_weak_htbl                      true
% 2.48/1.02  --gc_record_bc_elim                     false
% 2.48/1.02  
% 2.48/1.02  ------ Preprocessing Options
% 2.48/1.02  
% 2.48/1.02  --preprocessing_flag                    true
% 2.48/1.02  --time_out_prep_mult                    0.1
% 2.48/1.02  --splitting_mode                        input
% 2.48/1.02  --splitting_grd                         true
% 2.48/1.02  --splitting_cvd                         false
% 2.48/1.02  --splitting_cvd_svl                     false
% 2.48/1.02  --splitting_nvd                         32
% 2.48/1.02  --sub_typing                            true
% 2.48/1.02  --prep_gs_sim                           true
% 2.48/1.02  --prep_unflatten                        true
% 2.48/1.02  --prep_res_sim                          true
% 2.48/1.02  --prep_upred                            true
% 2.48/1.02  --prep_sem_filter                       exhaustive
% 2.48/1.02  --prep_sem_filter_out                   false
% 2.48/1.02  --pred_elim                             true
% 2.48/1.02  --res_sim_input                         true
% 2.48/1.02  --eq_ax_congr_red                       true
% 2.48/1.02  --pure_diseq_elim                       true
% 2.48/1.02  --brand_transform                       false
% 2.48/1.02  --non_eq_to_eq                          false
% 2.48/1.02  --prep_def_merge                        true
% 2.48/1.02  --prep_def_merge_prop_impl              false
% 2.48/1.02  --prep_def_merge_mbd                    true
% 2.48/1.02  --prep_def_merge_tr_red                 false
% 2.48/1.02  --prep_def_merge_tr_cl                  false
% 2.48/1.02  --smt_preprocessing                     true
% 2.48/1.02  --smt_ac_axioms                         fast
% 2.48/1.02  --preprocessed_out                      false
% 2.48/1.02  --preprocessed_stats                    false
% 2.48/1.02  
% 2.48/1.02  ------ Abstraction refinement Options
% 2.48/1.02  
% 2.48/1.02  --abstr_ref                             []
% 2.48/1.02  --abstr_ref_prep                        false
% 2.48/1.02  --abstr_ref_until_sat                   false
% 2.48/1.02  --abstr_ref_sig_restrict                funpre
% 2.48/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/1.02  --abstr_ref_under                       []
% 2.48/1.02  
% 2.48/1.02  ------ SAT Options
% 2.48/1.02  
% 2.48/1.02  --sat_mode                              false
% 2.48/1.02  --sat_fm_restart_options                ""
% 2.48/1.02  --sat_gr_def                            false
% 2.48/1.02  --sat_epr_types                         true
% 2.48/1.02  --sat_non_cyclic_types                  false
% 2.48/1.02  --sat_finite_models                     false
% 2.48/1.02  --sat_fm_lemmas                         false
% 2.48/1.02  --sat_fm_prep                           false
% 2.48/1.02  --sat_fm_uc_incr                        true
% 2.48/1.02  --sat_out_model                         small
% 2.48/1.02  --sat_out_clauses                       false
% 2.48/1.02  
% 2.48/1.02  ------ QBF Options
% 2.48/1.02  
% 2.48/1.02  --qbf_mode                              false
% 2.48/1.02  --qbf_elim_univ                         false
% 2.48/1.02  --qbf_dom_inst                          none
% 2.48/1.02  --qbf_dom_pre_inst                      false
% 2.48/1.02  --qbf_sk_in                             false
% 2.48/1.02  --qbf_pred_elim                         true
% 2.48/1.02  --qbf_split                             512
% 2.48/1.02  
% 2.48/1.02  ------ BMC1 Options
% 2.48/1.02  
% 2.48/1.02  --bmc1_incremental                      false
% 2.48/1.02  --bmc1_axioms                           reachable_all
% 2.48/1.02  --bmc1_min_bound                        0
% 2.48/1.02  --bmc1_max_bound                        -1
% 2.48/1.02  --bmc1_max_bound_default                -1
% 2.48/1.02  --bmc1_symbol_reachability              true
% 2.48/1.02  --bmc1_property_lemmas                  false
% 2.48/1.02  --bmc1_k_induction                      false
% 2.48/1.02  --bmc1_non_equiv_states                 false
% 2.48/1.02  --bmc1_deadlock                         false
% 2.48/1.02  --bmc1_ucm                              false
% 2.48/1.02  --bmc1_add_unsat_core                   none
% 2.48/1.02  --bmc1_unsat_core_children              false
% 2.48/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/1.02  --bmc1_out_stat                         full
% 2.48/1.02  --bmc1_ground_init                      false
% 2.48/1.02  --bmc1_pre_inst_next_state              false
% 2.48/1.02  --bmc1_pre_inst_state                   false
% 2.48/1.02  --bmc1_pre_inst_reach_state             false
% 2.48/1.02  --bmc1_out_unsat_core                   false
% 2.48/1.02  --bmc1_aig_witness_out                  false
% 2.48/1.02  --bmc1_verbose                          false
% 2.48/1.02  --bmc1_dump_clauses_tptp                false
% 2.48/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.48/1.02  --bmc1_dump_file                        -
% 2.48/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.48/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.48/1.02  --bmc1_ucm_extend_mode                  1
% 2.48/1.02  --bmc1_ucm_init_mode                    2
% 2.48/1.02  --bmc1_ucm_cone_mode                    none
% 2.48/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.48/1.02  --bmc1_ucm_relax_model                  4
% 2.48/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.48/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/1.02  --bmc1_ucm_layered_model                none
% 2.48/1.02  --bmc1_ucm_max_lemma_size               10
% 2.48/1.02  
% 2.48/1.02  ------ AIG Options
% 2.48/1.02  
% 2.48/1.02  --aig_mode                              false
% 2.48/1.02  
% 2.48/1.02  ------ Instantiation Options
% 2.48/1.02  
% 2.48/1.02  --instantiation_flag                    true
% 2.48/1.02  --inst_sos_flag                         false
% 2.48/1.02  --inst_sos_phase                        true
% 2.48/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/1.02  --inst_lit_sel_side                     none
% 2.48/1.02  --inst_solver_per_active                1400
% 2.48/1.02  --inst_solver_calls_frac                1.
% 2.48/1.02  --inst_passive_queue_type               priority_queues
% 2.48/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/1.02  --inst_passive_queues_freq              [25;2]
% 2.48/1.02  --inst_dismatching                      true
% 2.48/1.02  --inst_eager_unprocessed_to_passive     true
% 2.48/1.02  --inst_prop_sim_given                   true
% 2.48/1.02  --inst_prop_sim_new                     false
% 2.48/1.02  --inst_subs_new                         false
% 2.48/1.02  --inst_eq_res_simp                      false
% 2.48/1.02  --inst_subs_given                       false
% 2.48/1.02  --inst_orphan_elimination               true
% 2.48/1.02  --inst_learning_loop_flag               true
% 2.48/1.02  --inst_learning_start                   3000
% 2.48/1.02  --inst_learning_factor                  2
% 2.48/1.02  --inst_start_prop_sim_after_learn       3
% 2.48/1.02  --inst_sel_renew                        solver
% 2.48/1.02  --inst_lit_activity_flag                true
% 2.48/1.02  --inst_restr_to_given                   false
% 2.48/1.02  --inst_activity_threshold               500
% 2.48/1.02  --inst_out_proof                        true
% 2.48/1.02  
% 2.48/1.02  ------ Resolution Options
% 2.48/1.02  
% 2.48/1.02  --resolution_flag                       false
% 2.48/1.02  --res_lit_sel                           adaptive
% 2.48/1.02  --res_lit_sel_side                      none
% 2.48/1.02  --res_ordering                          kbo
% 2.48/1.02  --res_to_prop_solver                    active
% 2.48/1.02  --res_prop_simpl_new                    false
% 2.48/1.02  --res_prop_simpl_given                  true
% 2.48/1.02  --res_passive_queue_type                priority_queues
% 2.48/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/1.02  --res_passive_queues_freq               [15;5]
% 2.48/1.02  --res_forward_subs                      full
% 2.48/1.02  --res_backward_subs                     full
% 2.48/1.02  --res_forward_subs_resolution           true
% 2.48/1.02  --res_backward_subs_resolution          true
% 2.48/1.02  --res_orphan_elimination                true
% 2.48/1.02  --res_time_limit                        2.
% 2.48/1.02  --res_out_proof                         true
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Options
% 2.48/1.02  
% 2.48/1.02  --superposition_flag                    true
% 2.48/1.02  --sup_passive_queue_type                priority_queues
% 2.48/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.48/1.02  --demod_completeness_check              fast
% 2.48/1.02  --demod_use_ground                      true
% 2.48/1.02  --sup_to_prop_solver                    passive
% 2.48/1.02  --sup_prop_simpl_new                    true
% 2.48/1.02  --sup_prop_simpl_given                  true
% 2.48/1.02  --sup_fun_splitting                     false
% 2.48/1.02  --sup_smt_interval                      50000
% 2.48/1.02  
% 2.48/1.02  ------ Superposition Simplification Setup
% 2.48/1.02  
% 2.48/1.02  --sup_indices_passive                   []
% 2.48/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.02  --sup_full_bw                           [BwDemod]
% 2.48/1.02  --sup_immed_triv                        [TrivRules]
% 2.48/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.02  --sup_immed_bw_main                     []
% 2.48/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/1.02  
% 2.48/1.02  ------ Combination Options
% 2.48/1.02  
% 2.48/1.02  --comb_res_mult                         3
% 2.48/1.02  --comb_sup_mult                         2
% 2.48/1.02  --comb_inst_mult                        10
% 2.48/1.02  
% 2.48/1.02  ------ Debug Options
% 2.48/1.02  
% 2.48/1.02  --dbg_backtrace                         false
% 2.48/1.02  --dbg_dump_prop_clauses                 false
% 2.48/1.02  --dbg_dump_prop_clauses_file            -
% 2.48/1.02  --dbg_out_stat                          false
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  ------ Proving...
% 2.48/1.02  
% 2.48/1.02  
% 2.48/1.02  % SZS status Theorem for theBenchmark.p
% 2.48/1.02  
% 2.48/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/1.02  
% 2.48/1.02  fof(f9,conjecture,(
% 2.48/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f10,negated_conjecture,(
% 2.48/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 2.48/1.02    inference(negated_conjecture,[],[f9])).
% 2.48/1.02  
% 2.48/1.02  fof(f19,plain,(
% 2.48/1.02    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.48/1.02    inference(ennf_transformation,[],[f10])).
% 2.48/1.02  
% 2.48/1.02  fof(f20,plain,(
% 2.48/1.02    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.48/1.02    inference(flattening,[],[f19])).
% 2.48/1.02  
% 2.48/1.02  fof(f41,plain,(
% 2.48/1.02    ( ! [X4,X2,X0,X3] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => (k1_funct_1(X3,sK11) = X4 & r2_hidden(sK11,X2) & r2_hidden(sK11,X0))) )),
% 2.48/1.02    introduced(choice_axiom,[])).
% 2.48/1.02  
% 2.48/1.02  fof(f40,plain,(
% 2.48/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) => (~r2_hidden(sK10,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = sK10 & r2_hidden(X5,X2) & r2_hidden(X5,X0)))) )),
% 2.48/1.02    introduced(choice_axiom,[])).
% 2.48/1.02  
% 2.48/1.02  fof(f39,plain,(
% 2.48/1.02    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (~r2_hidden(X4,k7_relset_1(sK6,sK7,sK9,sK8)) & ? [X5] : (k1_funct_1(sK9,X5) = X4 & r2_hidden(X5,sK8) & r2_hidden(X5,sK6))) & k1_xboole_0 != sK7 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK9,sK6,sK7) & v1_funct_1(sK9))),
% 2.48/1.02    introduced(choice_axiom,[])).
% 2.48/1.02  
% 2.48/1.02  fof(f42,plain,(
% 2.48/1.02    (~r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) & (k1_funct_1(sK9,sK11) = sK10 & r2_hidden(sK11,sK8) & r2_hidden(sK11,sK6))) & k1_xboole_0 != sK7 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK9,sK6,sK7) & v1_funct_1(sK9)),
% 2.48/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f20,f41,f40,f39])).
% 2.48/1.02  
% 2.48/1.02  fof(f72,plain,(
% 2.48/1.02    k1_funct_1(sK9,sK11) = sK10),
% 2.48/1.02    inference(cnf_transformation,[],[f42])).
% 2.48/1.02  
% 2.48/1.02  fof(f5,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f13,plain,(
% 2.48/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.48/1.02    inference(ennf_transformation,[],[f5])).
% 2.48/1.02  
% 2.48/1.02  fof(f14,plain,(
% 2.48/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.48/1.02    inference(flattening,[],[f13])).
% 2.48/1.02  
% 2.48/1.02  fof(f31,plain,(
% 2.48/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.48/1.02    inference(nnf_transformation,[],[f14])).
% 2.48/1.02  
% 2.48/1.02  fof(f32,plain,(
% 2.48/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.48/1.02    inference(flattening,[],[f31])).
% 2.48/1.02  
% 2.48/1.02  fof(f55,plain,(
% 2.48/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f32])).
% 2.48/1.02  
% 2.48/1.02  fof(f76,plain,(
% 2.48/1.02    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.48/1.02    inference(equality_resolution,[],[f55])).
% 2.48/1.02  
% 2.48/1.02  fof(f66,plain,(
% 2.48/1.02    v1_funct_1(sK9)),
% 2.48/1.02    inference(cnf_transformation,[],[f42])).
% 2.48/1.02  
% 2.48/1.02  fof(f1,axiom,(
% 2.48/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f11,plain,(
% 2.48/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.48/1.02    inference(ennf_transformation,[],[f1])).
% 2.48/1.02  
% 2.48/1.02  fof(f43,plain,(
% 2.48/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.48/1.02    inference(cnf_transformation,[],[f11])).
% 2.48/1.02  
% 2.48/1.02  fof(f68,plain,(
% 2.48/1.02    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 2.48/1.02    inference(cnf_transformation,[],[f42])).
% 2.48/1.02  
% 2.48/1.02  fof(f3,axiom,(
% 2.48/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f48,plain,(
% 2.48/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.48/1.02    inference(cnf_transformation,[],[f3])).
% 2.48/1.02  
% 2.48/1.02  fof(f70,plain,(
% 2.48/1.02    r2_hidden(sK11,sK6)),
% 2.48/1.02    inference(cnf_transformation,[],[f42])).
% 2.48/1.02  
% 2.48/1.02  fof(f67,plain,(
% 2.48/1.02    v1_funct_2(sK9,sK6,sK7)),
% 2.48/1.02    inference(cnf_transformation,[],[f42])).
% 2.48/1.02  
% 2.48/1.02  fof(f8,axiom,(
% 2.48/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.48/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.02  
% 2.48/1.02  fof(f17,plain,(
% 2.48/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/1.03    inference(ennf_transformation,[],[f8])).
% 2.48/1.03  
% 2.48/1.03  fof(f18,plain,(
% 2.48/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/1.03    inference(flattening,[],[f17])).
% 2.48/1.03  
% 2.48/1.03  fof(f38,plain,(
% 2.48/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/1.03    inference(nnf_transformation,[],[f18])).
% 2.48/1.03  
% 2.48/1.03  fof(f60,plain,(
% 2.48/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/1.03    inference(cnf_transformation,[],[f38])).
% 2.48/1.03  
% 2.48/1.03  fof(f69,plain,(
% 2.48/1.03    k1_xboole_0 != sK7),
% 2.48/1.03    inference(cnf_transformation,[],[f42])).
% 2.48/1.03  
% 2.48/1.03  fof(f2,axiom,(
% 2.48/1.03    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f21,plain,(
% 2.48/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.48/1.03    inference(nnf_transformation,[],[f2])).
% 2.48/1.03  
% 2.48/1.03  fof(f22,plain,(
% 2.48/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.48/1.03    inference(rectify,[],[f21])).
% 2.48/1.03  
% 2.48/1.03  fof(f25,plain,(
% 2.48/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f24,plain,(
% 2.48/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0))) )),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f23,plain,(
% 2.48/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f26,plain,(
% 2.48/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).
% 2.48/1.03  
% 2.48/1.03  fof(f45,plain,(
% 2.48/1.03    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.48/1.03    inference(cnf_transformation,[],[f26])).
% 2.48/1.03  
% 2.48/1.03  fof(f74,plain,(
% 2.48/1.03    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.48/1.03    inference(equality_resolution,[],[f45])).
% 2.48/1.03  
% 2.48/1.03  fof(f7,axiom,(
% 2.48/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f16,plain,(
% 2.48/1.03    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.48/1.03    inference(ennf_transformation,[],[f7])).
% 2.48/1.03  
% 2.48/1.03  fof(f33,plain,(
% 2.48/1.03    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.48/1.03    inference(nnf_transformation,[],[f16])).
% 2.48/1.03  
% 2.48/1.03  fof(f34,plain,(
% 2.48/1.03    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.48/1.03    inference(rectify,[],[f33])).
% 2.48/1.03  
% 2.48/1.03  fof(f36,plain,(
% 2.48/1.03    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK5(X1,X2),X6),X2) & r2_hidden(sK5(X1,X2),X1)))),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f35,plain,(
% 2.48/1.03    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2))),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f37,plain,(
% 2.48/1.03    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK5(X1,X2),X6),X2) & r2_hidden(sK5(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f36,f35])).
% 2.48/1.03  
% 2.48/1.03  fof(f59,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK4(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.48/1.03    inference(cnf_transformation,[],[f37])).
% 2.48/1.03  
% 2.48/1.03  fof(f4,axiom,(
% 2.48/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f12,plain,(
% 2.48/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.48/1.03    inference(ennf_transformation,[],[f4])).
% 2.48/1.03  
% 2.48/1.03  fof(f27,plain,(
% 2.48/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.48/1.03    inference(nnf_transformation,[],[f12])).
% 2.48/1.03  
% 2.48/1.03  fof(f28,plain,(
% 2.48/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.48/1.03    inference(rectify,[],[f27])).
% 2.48/1.03  
% 2.48/1.03  fof(f29,plain,(
% 2.48/1.03    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 2.48/1.03    introduced(choice_axiom,[])).
% 2.48/1.03  
% 2.48/1.03  fof(f30,plain,(
% 2.48/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 2.48/1.03  
% 2.48/1.03  fof(f52,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.48/1.03    inference(cnf_transformation,[],[f30])).
% 2.48/1.03  
% 2.48/1.03  fof(f6,axiom,(
% 2.48/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.48/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/1.03  
% 2.48/1.03  fof(f15,plain,(
% 2.48/1.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.48/1.03    inference(ennf_transformation,[],[f6])).
% 2.48/1.03  
% 2.48/1.03  fof(f56,plain,(
% 2.48/1.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.48/1.03    inference(cnf_transformation,[],[f15])).
% 2.48/1.03  
% 2.48/1.03  fof(f73,plain,(
% 2.48/1.03    ~r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))),
% 2.48/1.03    inference(cnf_transformation,[],[f42])).
% 2.48/1.03  
% 2.48/1.03  fof(f71,plain,(
% 2.48/1.03    r2_hidden(sK11,sK8)),
% 2.48/1.03    inference(cnf_transformation,[],[f42])).
% 2.48/1.03  
% 2.48/1.03  cnf(c_24,negated_conjecture,
% 2.48/1.03      ( k1_funct_1(sK9,sK11) = sK10 ),
% 2.48/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_10,plain,
% 2.48/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.48/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.48/1.03      | ~ v1_funct_1(X1)
% 2.48/1.03      | ~ v1_relat_1(X1) ),
% 2.48/1.03      inference(cnf_transformation,[],[f76]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_30,negated_conjecture,
% 2.48/1.03      ( v1_funct_1(sK9) ),
% 2.48/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_324,plain,
% 2.48/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.48/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.48/1.03      | ~ v1_relat_1(X1)
% 2.48/1.03      | sK9 != X1 ),
% 2.48/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_325,plain,
% 2.48/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK9))
% 2.48/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
% 2.48/1.03      | ~ v1_relat_1(sK9) ),
% 2.48/1.03      inference(unflattening,[status(thm)],[c_324]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1084,plain,
% 2.48/1.03      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 2.48/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top
% 2.48/1.03      | v1_relat_1(sK9) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_326,plain,
% 2.48/1.03      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 2.48/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top
% 2.48/1.03      | v1_relat_1(sK9) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_769,plain,( X0 = X0 ),theory(equality) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1272,plain,
% 2.48/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_769]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_0,plain,
% 2.48/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.48/1.03      | ~ v1_relat_1(X1)
% 2.48/1.03      | v1_relat_1(X0) ),
% 2.48/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_28,negated_conjecture,
% 2.48/1.03      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 2.48/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_362,plain,
% 2.48/1.03      ( ~ v1_relat_1(X0)
% 2.48/1.03      | v1_relat_1(X1)
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0)
% 2.48/1.03      | sK9 != X1 ),
% 2.48/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_363,plain,
% 2.48/1.03      ( ~ v1_relat_1(X0)
% 2.48/1.03      | v1_relat_1(sK9)
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(X0) ),
% 2.48/1.03      inference(unflattening,[status(thm)],[c_362]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1267,plain,
% 2.48/1.03      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.48/1.03      | v1_relat_1(sK9)
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_363]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1395,plain,
% 2.48/1.03      ( ~ v1_relat_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | v1_relat_1(sK9)
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_1267]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1396,plain,
% 2.48/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | v1_relat_1(k2_zfmisc_1(sK6,sK7)) != iProver_top
% 2.48/1.03      | v1_relat_1(sK9) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1395]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_5,plain,
% 2.48/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.48/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1511,plain,
% 2.48/1.03      ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1512,plain,
% 2.48/1.03      ( v1_relat_1(k2_zfmisc_1(sK6,sK7)) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1511]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1750,plain,
% 2.48/1.03      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top
% 2.48/1.03      | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_1084,c_326,c_1272,c_1396,c_1512]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1751,plain,
% 2.48/1.03      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 2.48/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top ),
% 2.48/1.03      inference(renaming,[status(thm)],[c_1750]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1758,plain,
% 2.48/1.03      ( r2_hidden(k4_tarski(sK11,sK10),sK9) = iProver_top
% 2.48/1.03      | r2_hidden(sK11,k1_relat_1(sK9)) != iProver_top ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_24,c_1751]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_26,negated_conjecture,
% 2.48/1.03      ( r2_hidden(sK11,sK6) ),
% 2.48/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_34,plain,
% 2.48/1.03      ( r2_hidden(sK11,sK6) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_29,negated_conjecture,
% 2.48/1.03      ( v1_funct_2(sK9,sK6,sK7) ),
% 2.48/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_22,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.48/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.48/1.03      | k1_xboole_0 = X2 ),
% 2.48/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_377,plain,
% 2.48/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.48/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | sK9 != X0
% 2.48/1.03      | k1_xboole_0 = X2 ),
% 2.48/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_378,plain,
% 2.48/1.03      ( ~ v1_funct_2(sK9,X0,X1)
% 2.48/1.03      | k1_relset_1(X0,X1,sK9) = X0
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | k1_xboole_0 = X1 ),
% 2.48/1.03      inference(unflattening,[status(thm)],[c_377]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_590,plain,
% 2.48/1.03      ( k1_relset_1(X0,X1,sK9) = X0
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | sK9 != sK9
% 2.48/1.03      | sK7 != X1
% 2.48/1.03      | sK6 != X0
% 2.48/1.03      | k1_xboole_0 = X1 ),
% 2.48/1.03      inference(resolution_lifted,[status(thm)],[c_29,c_378]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_591,plain,
% 2.48/1.03      ( k1_relset_1(sK6,sK7,sK9) = sK6
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | k1_xboole_0 = sK7 ),
% 2.48/1.03      inference(unflattening,[status(thm)],[c_590]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_27,negated_conjecture,
% 2.48/1.03      ( k1_xboole_0 != sK7 ),
% 2.48/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_592,plain,
% 2.48/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | k1_relset_1(sK6,sK7,sK9) = sK6 ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_591,c_27]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_593,plain,
% 2.48/1.03      ( k1_relset_1(sK6,sK7,sK9) = sK6
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 2.48/1.03      inference(renaming,[status(thm)],[c_592]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_660,plain,
% 2.48/1.03      ( k1_relset_1(sK6,sK7,sK9) = sK6 ),
% 2.48/1.03      inference(equality_resolution_simp,[status(thm)],[c_593]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3,plain,
% 2.48/1.03      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.48/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1329,plain,
% 2.48/1.03      ( ~ r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9)
% 2.48/1.03      | r2_hidden(sK11,k1_relat_1(sK9)) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1330,plain,
% 2.48/1.03      ( r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9) != iProver_top
% 2.48/1.03      | r2_hidden(sK11,k1_relat_1(sK9)) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1329]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_14,plain,
% 2.48/1.03      ( ~ r2_hidden(X0,X1)
% 2.48/1.03      | r2_hidden(k4_tarski(X0,sK4(X2,X0)),X2)
% 2.48/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.48/1.03      | k1_relset_1(X1,X3,X2) != X1 ),
% 2.48/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_422,plain,
% 2.48/1.03      ( ~ r2_hidden(X0,X1)
% 2.48/1.03      | r2_hidden(k4_tarski(X0,sK4(X2,X0)),X2)
% 2.48/1.03      | k1_relset_1(X1,X3,X2) != X1
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | sK9 != X2 ),
% 2.48/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_423,plain,
% 2.48/1.03      ( ~ r2_hidden(X0,X1)
% 2.48/1.03      | r2_hidden(k4_tarski(X0,sK4(sK9,X0)),sK9)
% 2.48/1.03      | k1_relset_1(X1,X2,sK9) != X1
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 2.48/1.03      inference(unflattening,[status(thm)],[c_422]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1262,plain,
% 2.48/1.03      ( r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9)
% 2.48/1.03      | ~ r2_hidden(sK11,sK6)
% 2.48/1.03      | k1_relset_1(sK6,X0,sK9) != sK6
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK6,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_423]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1449,plain,
% 2.48/1.03      ( r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9)
% 2.48/1.03      | ~ r2_hidden(sK11,sK6)
% 2.48/1.03      | k1_relset_1(sK6,sK7,sK9) != sK6
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 2.48/1.03      inference(instantiation,[status(thm)],[c_1262]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1450,plain,
% 2.48/1.03      ( k1_relset_1(sK6,sK7,sK9) != sK6
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | r2_hidden(k4_tarski(sK11,sK4(sK9,sK11)),sK9) = iProver_top
% 2.48/1.03      | r2_hidden(sK11,sK6) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1872,plain,
% 2.48/1.03      ( r2_hidden(k4_tarski(sK11,sK10),sK9) = iProver_top ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_1758,c_34,c_660,c_1272,c_1330,c_1450]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_6,plain,
% 2.48/1.03      ( ~ r2_hidden(X0,X1)
% 2.48/1.03      | r2_hidden(X2,k9_relat_1(X3,X1))
% 2.48/1.03      | ~ r2_hidden(X0,k1_relat_1(X3))
% 2.48/1.03      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 2.48/1.03      | ~ v1_relat_1(X3) ),
% 2.48/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1091,plain,
% 2.48/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.48/1.03      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 2.48/1.03      | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
% 2.48/1.03      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 2.48/1.03      | v1_relat_1(X3) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1094,plain,
% 2.48/1.03      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.48/1.03      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1210,plain,
% 2.48/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.48/1.03      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 2.48/1.03      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 2.48/1.03      | v1_relat_1(X3) != iProver_top ),
% 2.48/1.03      inference(forward_subsumption_resolution,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_1091,c_1094]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_2633,plain,
% 2.48/1.03      ( r2_hidden(sK11,X0) != iProver_top
% 2.48/1.03      | r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top
% 2.48/1.03      | v1_relat_1(sK9) != iProver_top ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_1872,c_1210]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3240,plain,
% 2.48/1.03      ( r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top
% 2.48/1.03      | r2_hidden(sK11,X0) != iProver_top ),
% 2.48/1.03      inference(global_propositional_subsumption,
% 2.48/1.03                [status(thm)],
% 2.48/1.03                [c_2633,c_1272,c_1396,c_1512]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3241,plain,
% 2.48/1.03      ( r2_hidden(sK11,X0) != iProver_top
% 2.48/1.03      | r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top ),
% 2.48/1.03      inference(renaming,[status(thm)],[c_3240]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_13,plain,
% 2.48/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.48/1.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.48/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_413,plain,
% 2.48/1.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 2.48/1.03      | sK9 != X2 ),
% 2.48/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_414,plain,
% 2.48/1.03      ( k7_relset_1(X0,X1,sK9,X2) = k9_relat_1(sK9,X2)
% 2.48/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 2.48/1.03      inference(unflattening,[status(thm)],[c_413]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1317,plain,
% 2.48/1.03      ( k7_relset_1(sK6,sK7,sK9,X0) = k9_relat_1(sK9,X0) ),
% 2.48/1.03      inference(equality_resolution,[status(thm)],[c_414]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_23,negated_conjecture,
% 2.48/1.03      ( ~ r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
% 2.48/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1087,plain,
% 2.48/1.03      ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) != iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_1522,plain,
% 2.48/1.03      ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) != iProver_top ),
% 2.48/1.03      inference(demodulation,[status(thm)],[c_1317,c_1087]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_3248,plain,
% 2.48/1.03      ( r2_hidden(sK11,sK8) != iProver_top ),
% 2.48/1.03      inference(superposition,[status(thm)],[c_3241,c_1522]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_25,negated_conjecture,
% 2.48/1.03      ( r2_hidden(sK11,sK8) ),
% 2.48/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(c_35,plain,
% 2.48/1.03      ( r2_hidden(sK11,sK8) = iProver_top ),
% 2.48/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.48/1.03  
% 2.48/1.03  cnf(contradiction,plain,
% 2.48/1.03      ( $false ),
% 2.48/1.03      inference(minisat,[status(thm)],[c_3248,c_35]) ).
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/1.03  
% 2.48/1.03  ------                               Statistics
% 2.48/1.03  
% 2.48/1.03  ------ General
% 2.48/1.03  
% 2.48/1.03  abstr_ref_over_cycles:                  0
% 2.48/1.03  abstr_ref_under_cycles:                 0
% 2.48/1.03  gc_basic_clause_elim:                   0
% 2.48/1.03  forced_gc_time:                         0
% 2.48/1.03  parsing_time:                           0.011
% 2.48/1.03  unif_index_cands_time:                  0.
% 2.48/1.03  unif_index_add_time:                    0.
% 2.48/1.03  orderings_time:                         0.
% 2.48/1.03  out_proof_time:                         0.013
% 2.48/1.03  total_time:                             0.165
% 2.48/1.03  num_of_symbols:                         57
% 2.48/1.03  num_of_terms:                           4644
% 2.48/1.03  
% 2.48/1.03  ------ Preprocessing
% 2.48/1.03  
% 2.48/1.03  num_of_splits:                          0
% 2.48/1.03  num_of_split_atoms:                     0
% 2.48/1.03  num_of_reused_defs:                     0
% 2.48/1.03  num_eq_ax_congr_red:                    42
% 2.48/1.03  num_of_sem_filtered_clauses:            1
% 2.48/1.03  num_of_subtypes:                        0
% 2.48/1.03  monotx_restored_types:                  0
% 2.48/1.03  sat_num_of_epr_types:                   0
% 2.48/1.03  sat_num_of_non_cyclic_types:            0
% 2.48/1.03  sat_guarded_non_collapsed_types:        0
% 2.48/1.03  num_pure_diseq_elim:                    0
% 2.48/1.03  simp_replaced_by:                       0
% 2.48/1.03  res_preprocessed:                       131
% 2.48/1.03  prep_upred:                             0
% 2.48/1.03  prep_unflattend:                        29
% 2.48/1.03  smt_new_axioms:                         0
% 2.48/1.03  pred_elim_cands:                        2
% 2.48/1.03  pred_elim:                              3
% 2.48/1.03  pred_elim_cl:                           6
% 2.48/1.03  pred_elim_cycles:                       5
% 2.48/1.03  merged_defs:                            0
% 2.48/1.03  merged_defs_ncl:                        0
% 2.48/1.03  bin_hyper_res:                          0
% 2.48/1.03  prep_cycles:                            4
% 2.48/1.03  pred_elim_time:                         0.007
% 2.48/1.03  splitting_time:                         0.
% 2.48/1.03  sem_filter_time:                        0.
% 2.48/1.03  monotx_time:                            0.
% 2.48/1.03  subtype_inf_time:                       0.
% 2.48/1.03  
% 2.48/1.03  ------ Problem properties
% 2.48/1.03  
% 2.48/1.03  clauses:                                24
% 2.48/1.03  conjectures:                            5
% 2.48/1.03  epr:                                    3
% 2.48/1.03  horn:                                   21
% 2.48/1.03  ground:                                 8
% 2.48/1.03  unary:                                  7
% 2.48/1.03  binary:                                 3
% 2.48/1.03  lits:                                   59
% 2.48/1.03  lits_eq:                                22
% 2.48/1.03  fd_pure:                                0
% 2.48/1.03  fd_pseudo:                              0
% 2.48/1.03  fd_cond:                                0
% 2.48/1.03  fd_pseudo_cond:                         3
% 2.48/1.03  ac_symbols:                             0
% 2.48/1.03  
% 2.48/1.03  ------ Propositional Solver
% 2.48/1.03  
% 2.48/1.03  prop_solver_calls:                      26
% 2.48/1.03  prop_fast_solver_calls:                 824
% 2.48/1.03  smt_solver_calls:                       0
% 2.48/1.03  smt_fast_solver_calls:                  0
% 2.48/1.03  prop_num_of_clauses:                    1257
% 2.48/1.03  prop_preprocess_simplified:             4302
% 2.48/1.03  prop_fo_subsumed:                       13
% 2.48/1.03  prop_solver_time:                       0.
% 2.48/1.03  smt_solver_time:                        0.
% 2.48/1.03  smt_fast_solver_time:                   0.
% 2.48/1.03  prop_fast_solver_time:                  0.
% 2.48/1.03  prop_unsat_core_time:                   0.
% 2.48/1.03  
% 2.48/1.03  ------ QBF
% 2.48/1.03  
% 2.48/1.03  qbf_q_res:                              0
% 2.48/1.03  qbf_num_tautologies:                    0
% 2.48/1.03  qbf_prep_cycles:                        0
% 2.48/1.03  
% 2.48/1.03  ------ BMC1
% 2.48/1.03  
% 2.48/1.03  bmc1_current_bound:                     -1
% 2.48/1.03  bmc1_last_solved_bound:                 -1
% 2.48/1.03  bmc1_unsat_core_size:                   -1
% 2.48/1.03  bmc1_unsat_core_parents_size:           -1
% 2.48/1.03  bmc1_merge_next_fun:                    0
% 2.48/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.48/1.03  
% 2.48/1.03  ------ Instantiation
% 2.48/1.03  
% 2.48/1.03  inst_num_of_clauses:                    317
% 2.48/1.03  inst_num_in_passive:                    48
% 2.48/1.03  inst_num_in_active:                     184
% 2.48/1.03  inst_num_in_unprocessed:                85
% 2.48/1.03  inst_num_of_loops:                      200
% 2.48/1.03  inst_num_of_learning_restarts:          0
% 2.48/1.03  inst_num_moves_active_passive:          13
% 2.48/1.03  inst_lit_activity:                      0
% 2.48/1.03  inst_lit_activity_moves:                0
% 2.48/1.03  inst_num_tautologies:                   0
% 2.48/1.03  inst_num_prop_implied:                  0
% 2.48/1.03  inst_num_existing_simplified:           0
% 2.48/1.03  inst_num_eq_res_simplified:             0
% 2.48/1.03  inst_num_child_elim:                    0
% 2.48/1.03  inst_num_of_dismatching_blockings:      33
% 2.48/1.03  inst_num_of_non_proper_insts:           236
% 2.48/1.03  inst_num_of_duplicates:                 0
% 2.48/1.03  inst_inst_num_from_inst_to_res:         0
% 2.48/1.03  inst_dismatching_checking_time:         0.
% 2.48/1.03  
% 2.48/1.03  ------ Resolution
% 2.48/1.03  
% 2.48/1.03  res_num_of_clauses:                     0
% 2.48/1.03  res_num_in_passive:                     0
% 2.48/1.03  res_num_in_active:                      0
% 2.48/1.03  res_num_of_loops:                       135
% 2.48/1.03  res_forward_subset_subsumed:            25
% 2.48/1.03  res_backward_subset_subsumed:           0
% 2.48/1.03  res_forward_subsumed:                   0
% 2.48/1.03  res_backward_subsumed:                  0
% 2.48/1.03  res_forward_subsumption_resolution:     0
% 2.48/1.03  res_backward_subsumption_resolution:    0
% 2.48/1.03  res_clause_to_clause_subsumption:       104
% 2.48/1.03  res_orphan_elimination:                 0
% 2.48/1.03  res_tautology_del:                      40
% 2.48/1.03  res_num_eq_res_simplified:              1
% 2.48/1.03  res_num_sel_changes:                    0
% 2.48/1.03  res_moves_from_active_to_pass:          0
% 2.48/1.03  
% 2.48/1.03  ------ Superposition
% 2.48/1.03  
% 2.48/1.03  sup_time_total:                         0.
% 2.48/1.03  sup_time_generating:                    0.
% 2.48/1.03  sup_time_sim_full:                      0.
% 2.48/1.03  sup_time_sim_immed:                     0.
% 2.48/1.03  
% 2.48/1.03  sup_num_of_clauses:                     71
% 2.48/1.03  sup_num_in_active:                      38
% 2.48/1.03  sup_num_in_passive:                     33
% 2.48/1.03  sup_num_of_loops:                       38
% 2.48/1.03  sup_fw_superposition:                   30
% 2.48/1.03  sup_bw_superposition:                   25
% 2.48/1.03  sup_immediate_simplified:               7
% 2.48/1.03  sup_given_eliminated:                   0
% 2.48/1.03  comparisons_done:                       0
% 2.48/1.03  comparisons_avoided:                    2
% 2.48/1.03  
% 2.48/1.03  ------ Simplifications
% 2.48/1.03  
% 2.48/1.03  
% 2.48/1.03  sim_fw_subset_subsumed:                 3
% 2.48/1.03  sim_bw_subset_subsumed:                 0
% 2.48/1.03  sim_fw_subsumed:                        0
% 2.48/1.03  sim_bw_subsumed:                        1
% 2.48/1.03  sim_fw_subsumption_res:                 1
% 2.48/1.03  sim_bw_subsumption_res:                 0
% 2.48/1.03  sim_tautology_del:                      3
% 2.48/1.03  sim_eq_tautology_del:                   2
% 2.48/1.03  sim_eq_res_simp:                        1
% 2.48/1.03  sim_fw_demodulated:                     0
% 2.48/1.03  sim_bw_demodulated:                     1
% 2.48/1.03  sim_light_normalised:                   3
% 2.48/1.03  sim_joinable_taut:                      0
% 2.48/1.03  sim_joinable_simp:                      0
% 2.48/1.03  sim_ac_normalised:                      0
% 2.48/1.03  sim_smt_subsumption:                    0
% 2.48/1.03  
%------------------------------------------------------------------------------

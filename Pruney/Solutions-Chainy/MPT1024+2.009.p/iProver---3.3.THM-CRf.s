%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:49 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  220 (14116 expanded)
%              Number of clauses        :  154 (4806 expanded)
%              Number of leaves         :   22 (3301 expanded)
%              Depth                    :   35
%              Number of atoms          :  676 (70736 expanded)
%              Number of equality atoms :  369 (18163 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f39,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK2(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
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
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ r2_hidden(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ r2_hidden(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f29,f43,f42])).

fof(f71,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f61,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_782,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_780,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_760,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1920,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_760])).

cnf(c_5460,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_1920])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_769,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1381,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_769])).

cnf(c_1914,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_782,c_1381])).

cnf(c_5461,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5460,c_1914])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1866,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK2(X0,X2),X0)
    | r2_hidden(sK2(X0,X2),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1)))
    | ~ r2_hidden(sK2(X0,X2),X0)
    | r2_hidden(sK2(X0,X2),k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_2223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1))) != iProver_top
    | r2_hidden(sK2(X0,X2),X0) != iProver_top
    | r2_hidden(sK2(X0,X2),k1_relat_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2221])).

cnf(c_2225,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) != iProver_top
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2223])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK2(X1,X0),X1)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_765,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK2(X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2782,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | r2_hidden(sK2(X0,X2),X0) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_765])).

cnf(c_5469,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = X0
    | r2_hidden(sK2(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_2782])).

cnf(c_5470,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK2(X0,k1_xboole_0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5469,c_1914])).

cnf(c_5472,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5470])).

cnf(c_6299,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1)))
    | ~ r1_tarski(X0,k1_relat_1(X1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6300,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6299])).

cnf(c_6302,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6300])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_776,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_756,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_759,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1217,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_759])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1233,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1217])).

cnf(c_1625,plain,
    ( sK4 = k1_xboole_0
    | k1_relset_1(sK3,sK4,sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1217,c_27,c_1233])).

cnf(c_1626,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1625])).

cnf(c_1382,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_756,c_769])).

cnf(c_1627,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1626,c_1382])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_774,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2939,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_774])).

cnf(c_31,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1048,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1049,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1048])).

cnf(c_3400,plain,
    ( r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2939,c_31,c_1049])).

cnf(c_3401,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3400])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_768,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1480,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_756,c_768])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_757,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1547,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1480,c_757])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_775,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_772,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4205,plain,
    ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
    | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_772])).

cnf(c_6762,plain,
    ( k1_funct_1(sK6,sK0(sK7,sK5,sK6)) = sK7
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_4205])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7198,plain,
    ( k1_funct_1(sK6,sK0(sK7,sK5,sK6)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6762,c_29,c_31,c_1049])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_758,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7202,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),sK3) != iProver_top
    | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7198,c_758])).

cnf(c_7383,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3401,c_7202])).

cnf(c_7410,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7383,c_1547])).

cnf(c_7411,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_7410])).

cnf(c_7416,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_7411])).

cnf(c_7621,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7416,c_31,c_1049,c_1547])).

cnf(c_7642,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7621,c_756])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_763,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7891,plain,
    ( sK3 = k1_xboole_0
    | sK6 = k1_xboole_0
    | v1_funct_2(sK6,sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7642,c_763])).

cnf(c_30,plain,
    ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_269,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_296,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_1308,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_270,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1534,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_1535,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_282,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1176,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | X2 != sK4
    | X1 != sK3
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1307,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | X1 != sK4
    | X0 != sK3
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_2130,plain,
    ( v1_funct_2(sK6,sK3,X0)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | X0 != sK4
    | sK3 != sK3
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_2132,plain,
    ( X0 != sK4
    | sK3 != sK3
    | sK6 != sK6
    | v1_funct_2(sK6,sK3,X0) = iProver_top
    | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2130])).

cnf(c_2134,plain,
    ( sK3 != sK3
    | sK6 != sK6
    | k1_xboole_0 != sK4
    | v1_funct_2(sK6,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_2131,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_8142,plain,
    ( sK6 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7891,c_30,c_31,c_296,c_1049,c_1308,c_1535,c_1547,c_2134,c_2131,c_7416])).

cnf(c_8143,plain,
    ( sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8142])).

cnf(c_8148,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8143,c_7642])).

cnf(c_276,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_288,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_1019,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1020,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_1022,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_1314,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1315,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1314])).

cnf(c_1317,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1126,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_1661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_3069,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_3070,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK6 != X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3069])).

cnf(c_3072,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK6 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3070])).

cnf(c_273,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_5840,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_8540,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8148,c_288,c_296,c_1022,c_1317,c_3072,c_5840])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_773,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(sK2(X1,X0),X3),X0)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_766,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X2),X3),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4423,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK2(X0,X2),k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_766])).

cnf(c_770,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10623,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK2(X0,X2),k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4423,c_770])).

cnf(c_10628,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0,sK6),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8540,c_10623])).

cnf(c_8551,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_8540,c_769])).

cnf(c_10640,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0,sK6),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10628,c_8551])).

cnf(c_16011,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK6),k1_relat_1(sK6)) != iProver_top
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10640,c_29])).

cnf(c_16012,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0,sK6),k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16011])).

cnf(c_755,plain,
    ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7643,plain,
    ( v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7621,c_755])).

cnf(c_8149,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8143,c_7643])).

cnf(c_8553,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8540,c_760])).

cnf(c_8559,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8551,c_8553])).

cnf(c_12164,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8149,c_8559])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_767,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4454,plain,
    ( k1_relat_1(sK6) != sK3
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_767])).

cnf(c_4672,plain,
    ( k1_relat_1(sK6) != sK3
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4454,c_31])).

cnf(c_12176,plain,
    ( sK3 != k1_xboole_0
    | sK6 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_12164,c_4672])).

cnf(c_101,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_103,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_781,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2044,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_781])).

cnf(c_2940,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X3) = iProver_top
    | r1_tarski(k1_relat_1(X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_2044])).

cnf(c_8899,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2940,c_7202])).

cnf(c_9562,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
    | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8899,c_31,c_1049,c_1547])).

cnf(c_9563,plain,
    ( r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_9562])).

cnf(c_9568,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_9563])).

cnf(c_9778,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9568,c_31,c_1049,c_1547])).

cnf(c_9784,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8143,c_9778])).

cnf(c_12173,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12164,c_9784])).

cnf(c_12337,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12176,c_103,c_12173])).

cnf(c_16015,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16012,c_12337])).

cnf(c_16552,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_16555,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16552])).

cnf(c_16557,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_16555])).

cnf(c_17260,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5461,c_2225,c_5472,c_6302,c_16015,c_16557])).

cnf(c_12355,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12337,c_9778])).

cnf(c_17272,plain,
    ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17260,c_12355])).

cnf(c_24179,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17272,c_782])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.60/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.60/1.48  
% 7.60/1.48  ------  iProver source info
% 7.60/1.48  
% 7.60/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.60/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.60/1.48  git: non_committed_changes: false
% 7.60/1.48  git: last_make_outside_of_git: false
% 7.60/1.48  
% 7.60/1.48  ------ 
% 7.60/1.48  ------ Parsing...
% 7.60/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  ------ Proving...
% 7.60/1.48  ------ Problem Properties 
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  clauses                                 29
% 7.60/1.48  conjectures                             5
% 7.60/1.48  EPR                                     3
% 7.60/1.48  Horn                                    24
% 7.60/1.48  unary                                   6
% 7.60/1.48  binary                                  4
% 7.60/1.48  lits                                    80
% 7.60/1.48  lits eq                                 16
% 7.60/1.48  fd_pure                                 0
% 7.60/1.48  fd_pseudo                               0
% 7.60/1.48  fd_cond                                 3
% 7.60/1.48  fd_pseudo_cond                          1
% 7.60/1.48  AC symbols                              0
% 7.60/1.48  
% 7.60/1.48  ------ Input Options Time Limit: Unbounded
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ 
% 7.60/1.48  Current options:
% 7.60/1.48  ------ 
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  % SZS status Theorem for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48   Resolution empty clause
% 7.60/1.48  
% 7.60/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  fof(f1,axiom,(
% 7.60/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f45,plain,(
% 7.60/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f1])).
% 7.60/1.48  
% 7.60/1.48  fof(f3,axiom,(
% 7.60/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f15,plain,(
% 7.60/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.60/1.48    inference(unused_predicate_definition_removal,[],[f3])).
% 7.60/1.48  
% 7.60/1.48  fof(f17,plain,(
% 7.60/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.60/1.48    inference(ennf_transformation,[],[f15])).
% 7.60/1.48  
% 7.60/1.48  fof(f47,plain,(
% 7.60/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f17])).
% 7.60/1.48  
% 7.60/1.48  fof(f12,axiom,(
% 7.60/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f26,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.60/1.48    inference(ennf_transformation,[],[f12])).
% 7.60/1.48  
% 7.60/1.48  fof(f27,plain,(
% 7.60/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.60/1.48    inference(flattening,[],[f26])).
% 7.60/1.48  
% 7.60/1.48  fof(f41,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.60/1.48    inference(nnf_transformation,[],[f27])).
% 7.60/1.48  
% 7.60/1.48  fof(f64,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f41])).
% 7.60/1.48  
% 7.60/1.48  fof(f79,plain,(
% 7.60/1.48    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.60/1.48    inference(equality_resolution,[],[f64])).
% 7.60/1.48  
% 7.60/1.48  fof(f9,axiom,(
% 7.60/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f23,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.60/1.48    inference(ennf_transformation,[],[f9])).
% 7.60/1.48  
% 7.60/1.48  fof(f58,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f23])).
% 7.60/1.48  
% 7.60/1.48  fof(f2,axiom,(
% 7.60/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f16,plain,(
% 7.60/1.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f2])).
% 7.60/1.48  
% 7.60/1.48  fof(f46,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f16])).
% 7.60/1.48  
% 7.60/1.48  fof(f11,axiom,(
% 7.60/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f25,plain,(
% 7.60/1.48    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.60/1.48    inference(ennf_transformation,[],[f11])).
% 7.60/1.48  
% 7.60/1.48  fof(f36,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.60/1.48    inference(nnf_transformation,[],[f25])).
% 7.60/1.48  
% 7.60/1.48  fof(f37,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.60/1.48    inference(rectify,[],[f36])).
% 7.60/1.48  
% 7.60/1.48  fof(f39,plain,(
% 7.60/1.48    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f38,plain,(
% 7.60/1.48    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2))),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f40,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.60/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).
% 7.60/1.48  
% 7.60/1.48  fof(f60,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK2(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f40])).
% 7.60/1.48  
% 7.60/1.48  fof(f6,axiom,(
% 7.60/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f19,plain,(
% 7.60/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.60/1.48    inference(ennf_transformation,[],[f6])).
% 7.60/1.48  
% 7.60/1.48  fof(f30,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.60/1.48    inference(nnf_transformation,[],[f19])).
% 7.60/1.48  
% 7.60/1.48  fof(f31,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.60/1.48    inference(rectify,[],[f30])).
% 7.60/1.48  
% 7.60/1.48  fof(f32,plain,(
% 7.60/1.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f33,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.60/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 7.60/1.48  
% 7.60/1.48  fof(f52,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f33])).
% 7.60/1.48  
% 7.60/1.48  fof(f13,conjecture,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f14,negated_conjecture,(
% 7.60/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.60/1.48    inference(negated_conjecture,[],[f13])).
% 7.60/1.48  
% 7.60/1.48  fof(f28,plain,(
% 7.60/1.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.60/1.48    inference(ennf_transformation,[],[f14])).
% 7.60/1.48  
% 7.60/1.48  fof(f29,plain,(
% 7.60/1.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.60/1.48    inference(flattening,[],[f28])).
% 7.60/1.48  
% 7.60/1.48  fof(f43,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f42,plain,(
% 7.60/1.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f44,plain,(
% 7.60/1.48    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 7.60/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f29,f43,f42])).
% 7.60/1.48  
% 7.60/1.48  fof(f71,plain,(
% 7.60/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f63,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f41])).
% 7.60/1.48  
% 7.60/1.48  fof(f70,plain,(
% 7.60/1.48    v1_funct_2(sK6,sK3,sK4)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f50,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f33])).
% 7.60/1.48  
% 7.60/1.48  fof(f8,axiom,(
% 7.60/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f22,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.60/1.48    inference(ennf_transformation,[],[f8])).
% 7.60/1.48  
% 7.60/1.48  fof(f57,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f22])).
% 7.60/1.48  
% 7.60/1.48  fof(f10,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f24,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.60/1.48    inference(ennf_transformation,[],[f10])).
% 7.60/1.48  
% 7.60/1.48  fof(f59,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f24])).
% 7.60/1.48  
% 7.60/1.48  fof(f72,plain,(
% 7.60/1.48    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f51,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f33])).
% 7.60/1.48  
% 7.60/1.48  fof(f7,axiom,(
% 7.60/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f20,plain,(
% 7.60/1.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.60/1.48    inference(ennf_transformation,[],[f7])).
% 7.60/1.48  
% 7.60/1.48  fof(f21,plain,(
% 7.60/1.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.60/1.48    inference(flattening,[],[f20])).
% 7.60/1.48  
% 7.60/1.48  fof(f34,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.60/1.48    inference(nnf_transformation,[],[f21])).
% 7.60/1.48  
% 7.60/1.48  fof(f35,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.60/1.48    inference(flattening,[],[f34])).
% 7.60/1.48  
% 7.60/1.48  fof(f55,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f69,plain,(
% 7.60/1.48    v1_funct_1(sK6)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f73,plain,(
% 7.60/1.48    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f67,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f41])).
% 7.60/1.48  
% 7.60/1.48  fof(f77,plain,(
% 7.60/1.48    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.60/1.48    inference(equality_resolution,[],[f67])).
% 7.60/1.48  
% 7.60/1.48  fof(f56,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f74,plain,(
% 7.60/1.48    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.60/1.48    inference(equality_resolution,[],[f56])).
% 7.60/1.48  
% 7.60/1.48  fof(f61,plain,(
% 7.60/1.48    ( ! [X6,X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f40])).
% 7.60/1.48  
% 7.60/1.48  fof(f62,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f40])).
% 7.60/1.48  
% 7.60/1.48  cnf(c_0,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_782,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2,plain,
% 7.60/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_780,plain,
% 7.60/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.60/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_22,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.60/1.48      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.60/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_760,plain,
% 7.60/1.48      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.60/1.48      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.60/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1920,plain,
% 7.60/1.48      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.60/1.48      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.60/1.48      | r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_780,c_760]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5460,plain,
% 7.60/1.48      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0
% 7.60/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_782,c_1920]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_13,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_769,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1381,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.60/1.48      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_780,c_769]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1914,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_782,c_1381]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5461,plain,
% 7.60/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.60/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) != iProver_top ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_5460,c_1914]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.60/1.48      | ~ r2_hidden(X2,X0)
% 7.60/1.48      | r2_hidden(X2,X1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1866,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.60/1.48      | ~ r2_hidden(sK2(X0,X2),X0)
% 7.60/1.48      | r2_hidden(sK2(X0,X2),X1) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2221,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1)))
% 7.60/1.48      | ~ r2_hidden(sK2(X0,X2),X0)
% 7.60/1.48      | r2_hidden(sK2(X0,X2),k1_relat_1(X1)) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1866]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2223,plain,
% 7.60/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1))) != iProver_top
% 7.60/1.48      | r2_hidden(sK2(X0,X2),X0) != iProver_top
% 7.60/1.48      | r2_hidden(sK2(X0,X2),k1_relat_1(X1)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_2221]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2225,plain,
% 7.60/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) != iProver_top
% 7.60/1.48      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.60/1.48      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_2223]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_17,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | r2_hidden(sK2(X1,X0),X1)
% 7.60/1.48      | k1_relset_1(X1,X2,X0) = X1 ),
% 7.60/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_765,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.48      | r2_hidden(sK2(X0,X2),X0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2782,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.60/1.48      | r2_hidden(sK2(X0,X2),X0) = iProver_top
% 7.60/1.48      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_780,c_765]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5469,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
% 7.60/1.48      | r2_hidden(sK2(X0,k1_xboole_0),X0) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_782,c_2782]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5470,plain,
% 7.60/1.48      ( k1_relat_1(k1_xboole_0) = X0
% 7.60/1.48      | r2_hidden(sK2(X0,k1_xboole_0),X0) = iProver_top ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_5469,c_1914]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5472,plain,
% 7.60/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.60/1.48      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_5470]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6299,plain,
% 7.60/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1)))
% 7.60/1.48      | ~ r1_tarski(X0,k1_relat_1(X1)) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6300,plain,
% 7.60/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(X1))) = iProver_top
% 7.60/1.48      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_6299]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6302,plain,
% 7.60/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) = iProver_top
% 7.60/1.48      | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_6300]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6,plain,
% 7.60/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.60/1.48      | r2_hidden(sK0(X0,X2,X1),X2)
% 7.60/1.48      | ~ v1_relat_1(X1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_776,plain,
% 7.60/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.60/1.48      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 7.60/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_26,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.60/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_756,plain,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_23,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.60/1.48      | k1_xboole_0 = X2 ),
% 7.60/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_759,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.60/1.48      | k1_xboole_0 = X1
% 7.60/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1217,plain,
% 7.60/1.48      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 7.60/1.48      | sK4 = k1_xboole_0
% 7.60/1.48      | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_756,c_759]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_27,negated_conjecture,
% 7.60/1.48      ( v1_funct_2(sK6,sK3,sK4) ),
% 7.60/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1233,plain,
% 7.60/1.48      ( ~ v1_funct_2(sK6,sK3,sK4)
% 7.60/1.48      | k1_relset_1(sK3,sK4,sK6) = sK3
% 7.60/1.48      | sK4 = k1_xboole_0 ),
% 7.60/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_1217]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1625,plain,
% 7.60/1.48      ( sK4 = k1_xboole_0 | k1_relset_1(sK3,sK4,sK6) = sK3 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_1217,c_27,c_1233]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1626,plain,
% 7.60/1.48      ( k1_relset_1(sK3,sK4,sK6) = sK3 | sK4 = k1_xboole_0 ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_1625]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1382,plain,
% 7.60/1.48      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_756,c_769]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1627,plain,
% 7.60/1.48      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_1626,c_1382]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8,plain,
% 7.60/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.60/1.48      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 7.60/1.48      | ~ v1_relat_1(X1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_774,plain,
% 7.60/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.60/1.48      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 7.60/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2939,plain,
% 7.60/1.48      ( sK4 = k1_xboole_0
% 7.60/1.48      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 7.60/1.48      | r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top
% 7.60/1.48      | v1_relat_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1627,c_774]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_31,plain,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1048,plain,
% 7.60/1.48      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.60/1.48      | v1_relat_1(sK6) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1049,plain,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.60/1.48      | v1_relat_1(sK6) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1048]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3400,plain,
% 7.60/1.48      ( r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top
% 7.60/1.48      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 7.60/1.48      | sK4 = k1_xboole_0 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_2939,c_31,c_1049]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3401,plain,
% 7.60/1.48      ( sK4 = k1_xboole_0
% 7.60/1.48      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 7.60/1.48      | r2_hidden(sK0(X0,X1,sK6),sK3) = iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_3400]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_14,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_768,plain,
% 7.60/1.48      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1480,plain,
% 7.60/1.48      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_756,c_768]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_25,negated_conjecture,
% 7.60/1.48      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_757,plain,
% 7.60/1.48      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1547,plain,
% 7.60/1.48      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_1480,c_757]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7,plain,
% 7.60/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.60/1.48      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 7.60/1.48      | ~ v1_relat_1(X1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_775,plain,
% 7.60/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.60/1.48      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 7.60/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10,plain,
% 7.60/1.48      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.60/1.48      | ~ v1_funct_1(X2)
% 7.60/1.48      | ~ v1_relat_1(X2)
% 7.60/1.48      | k1_funct_1(X2,X0) = X1 ),
% 7.60/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_772,plain,
% 7.60/1.48      ( k1_funct_1(X0,X1) = X2
% 7.60/1.48      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 7.60/1.48      | v1_funct_1(X0) != iProver_top
% 7.60/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4205,plain,
% 7.60/1.48      ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
% 7.60/1.48      | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
% 7.60/1.48      | v1_funct_1(X0) != iProver_top
% 7.60/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_775,c_772]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6762,plain,
% 7.60/1.48      ( k1_funct_1(sK6,sK0(sK7,sK5,sK6)) = sK7
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top
% 7.60/1.48      | v1_relat_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1547,c_4205]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_28,negated_conjecture,
% 7.60/1.48      ( v1_funct_1(sK6) ),
% 7.60/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_29,plain,
% 7.60/1.48      ( v1_funct_1(sK6) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7198,plain,
% 7.60/1.48      ( k1_funct_1(sK6,sK0(sK7,sK5,sK6)) = sK7 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_6762,c_29,c_31,c_1049]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_24,negated_conjecture,
% 7.60/1.48      ( ~ r2_hidden(X0,sK3) | ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,X0) != sK7 ),
% 7.60/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_758,plain,
% 7.60/1.48      ( k1_funct_1(sK6,X0) != sK7
% 7.60/1.48      | r2_hidden(X0,sK3) != iProver_top
% 7.60/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7202,plain,
% 7.60/1.48      ( r2_hidden(sK0(sK7,sK5,sK6),sK3) != iProver_top
% 7.60/1.48      | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_7198,c_758]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7383,plain,
% 7.60/1.48      ( sK4 = k1_xboole_0
% 7.60/1.48      | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
% 7.60/1.48      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_3401,c_7202]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7410,plain,
% 7.60/1.48      ( r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top | sK4 = k1_xboole_0 ),
% 7.60/1.48      inference(global_propositional_subsumption,[status(thm)],[c_7383,c_1547]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7411,plain,
% 7.60/1.48      ( sK4 = k1_xboole_0 | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_7410]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7416,plain,
% 7.60/1.48      ( sK4 = k1_xboole_0
% 7.60/1.48      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 7.60/1.48      | v1_relat_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_776,c_7411]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7621,plain,
% 7.60/1.48      ( sK4 = k1_xboole_0 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_7416,c_31,c_1049,c_1547]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7642,plain,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_7621,c_756]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_19,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.60/1.48      | k1_xboole_0 = X1
% 7.60/1.48      | k1_xboole_0 = X0 ),
% 7.60/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_763,plain,
% 7.60/1.48      ( k1_xboole_0 = X0
% 7.60/1.48      | k1_xboole_0 = X1
% 7.60/1.48      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 7.60/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7891,plain,
% 7.60/1.48      ( sK3 = k1_xboole_0
% 7.60/1.48      | sK6 = k1_xboole_0
% 7.60/1.48      | v1_funct_2(sK6,sK3,k1_xboole_0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_7642,c_763]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_30,plain,
% 7.60/1.48      ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_269,plain,( X0 = X0 ),theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_296,plain,
% 7.60/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_269]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1308,plain,
% 7.60/1.48      ( sK6 = sK6 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_269]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_270,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1534,plain,
% 7.60/1.48      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_270]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1535,plain,
% 7.60/1.48      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1534]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_282,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.60/1.48      | v1_funct_2(X3,X4,X5)
% 7.60/1.48      | X3 != X0
% 7.60/1.48      | X4 != X1
% 7.60/1.48      | X5 != X2 ),
% 7.60/1.48      theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1176,plain,
% 7.60/1.48      ( v1_funct_2(X0,X1,X2)
% 7.60/1.48      | ~ v1_funct_2(sK6,sK3,sK4)
% 7.60/1.48      | X2 != sK4
% 7.60/1.48      | X1 != sK3
% 7.60/1.48      | X0 != sK6 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_282]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1307,plain,
% 7.60/1.48      ( v1_funct_2(sK6,X0,X1)
% 7.60/1.48      | ~ v1_funct_2(sK6,sK3,sK4)
% 7.60/1.48      | X1 != sK4
% 7.60/1.48      | X0 != sK3
% 7.60/1.48      | sK6 != sK6 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1176]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2130,plain,
% 7.60/1.48      ( v1_funct_2(sK6,sK3,X0)
% 7.60/1.48      | ~ v1_funct_2(sK6,sK3,sK4)
% 7.60/1.48      | X0 != sK4
% 7.60/1.48      | sK3 != sK3
% 7.60/1.48      | sK6 != sK6 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1307]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2132,plain,
% 7.60/1.48      ( X0 != sK4
% 7.60/1.48      | sK3 != sK3
% 7.60/1.48      | sK6 != sK6
% 7.60/1.48      | v1_funct_2(sK6,sK3,X0) = iProver_top
% 7.60/1.48      | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_2130]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2134,plain,
% 7.60/1.48      ( sK3 != sK3
% 7.60/1.48      | sK6 != sK6
% 7.60/1.48      | k1_xboole_0 != sK4
% 7.60/1.48      | v1_funct_2(sK6,sK3,sK4) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_2132]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2131,plain,
% 7.60/1.48      ( sK3 = sK3 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_269]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8142,plain,
% 7.60/1.48      ( sK6 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_7891,c_30,c_31,c_296,c_1049,c_1308,c_1535,c_1547,c_2134,
% 7.60/1.48                 c_2131,c_7416]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8143,plain,
% 7.60/1.48      ( sK3 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_8142]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8148,plain,
% 7.60/1.48      ( sK6 = k1_xboole_0
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_8143,c_7642]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_276,plain,
% 7.60/1.48      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 7.60/1.48      theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_288,plain,
% 7.60/1.48      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.60/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_276]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1019,plain,
% 7.60/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.60/1.48      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1020,plain,
% 7.60/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
% 7.60/1.48      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1022,plain,
% 7.60/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 7.60/1.48      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1020]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1314,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1315,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1314]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1317,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1315]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_274,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.60/1.48      theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1126,plain,
% 7.60/1.48      ( m1_subset_1(X0,X1)
% 7.60/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 7.60/1.48      | X0 != X2
% 7.60/1.48      | X1 != k1_zfmisc_1(X3) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_274]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1661,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.60/1.48      | X2 != X0
% 7.60/1.48      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1126]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3069,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 7.60/1.48      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 7.60/1.48      | sK6 != X0 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1661]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3070,plain,
% 7.60/1.48      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 7.60/1.48      | sK6 != X0
% 7.60/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_3069]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3072,plain,
% 7.60/1.48      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 7.60/1.48      | sK6 != k1_xboole_0
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 7.60/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_3070]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_273,plain,
% 7.60/1.48      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.60/1.48      theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5840,plain,
% 7.60/1.48      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 7.60/1.48      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_273]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8540,plain,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_8148,c_288,c_296,c_1022,c_1317,c_3072,c_5840]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_9,plain,
% 7.60/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.60/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.60/1.48      | ~ v1_funct_1(X1)
% 7.60/1.48      | ~ v1_relat_1(X1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_773,plain,
% 7.60/1.48      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.60/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 7.60/1.48      | v1_funct_1(X1) != iProver_top
% 7.60/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_16,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | ~ r2_hidden(k4_tarski(sK2(X1,X0),X3),X0)
% 7.60/1.48      | k1_relset_1(X1,X2,X0) = X1 ),
% 7.60/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_766,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.48      | r2_hidden(k4_tarski(sK2(X0,X2),X3),X2) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4423,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.48      | r2_hidden(sK2(X0,X2),k1_relat_1(X2)) != iProver_top
% 7.60/1.48      | v1_funct_1(X2) != iProver_top
% 7.60/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_773,c_766]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_770,plain,
% 7.60/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.60/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10623,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.48      | r2_hidden(sK2(X0,X2),k1_relat_1(X2)) != iProver_top
% 7.60/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.60/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_4423,c_770]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10628,plain,
% 7.60/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 7.60/1.48      | r2_hidden(sK2(k1_xboole_0,sK6),k1_relat_1(sK6)) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_8540,c_10623]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8551,plain,
% 7.60/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_8540,c_769]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10640,plain,
% 7.60/1.48      ( k1_relat_1(sK6) = k1_xboole_0
% 7.60/1.48      | r2_hidden(sK2(k1_xboole_0,sK6),k1_relat_1(sK6)) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_10628,c_8551]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_16011,plain,
% 7.60/1.48      ( r2_hidden(sK2(k1_xboole_0,sK6),k1_relat_1(sK6)) != iProver_top
% 7.60/1.48      | k1_relat_1(sK6) = k1_xboole_0 ),
% 7.60/1.48      inference(global_propositional_subsumption,[status(thm)],[c_10640,c_29]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_16012,plain,
% 7.60/1.48      ( k1_relat_1(sK6) = k1_xboole_0
% 7.60/1.48      | r2_hidden(sK2(k1_xboole_0,sK6),k1_relat_1(sK6)) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_16011]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_755,plain,
% 7.60/1.48      ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7643,plain,
% 7.60/1.48      ( v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_7621,c_755]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8149,plain,
% 7.60/1.48      ( sK6 = k1_xboole_0
% 7.60/1.48      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_8143,c_7643]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8553,plain,
% 7.60/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 7.60/1.48      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_8540,c_760]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8559,plain,
% 7.60/1.48      ( k1_relat_1(sK6) = k1_xboole_0
% 7.60/1.48      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_8551,c_8553]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12164,plain,
% 7.60/1.48      ( k1_relat_1(sK6) = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_8149,c_8559]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_15,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | ~ r2_hidden(X3,X1)
% 7.60/1.48      | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
% 7.60/1.48      | k1_relset_1(X1,X2,X0) != X1 ),
% 7.60/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_767,plain,
% 7.60/1.48      ( k1_relset_1(X0,X1,X2) != X0
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.48      | r2_hidden(X3,X0) != iProver_top
% 7.60/1.48      | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4454,plain,
% 7.60/1.48      ( k1_relat_1(sK6) != sK3
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.60/1.48      | r2_hidden(X0,sK3) != iProver_top
% 7.60/1.48      | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1382,c_767]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4672,plain,
% 7.60/1.48      ( k1_relat_1(sK6) != sK3
% 7.60/1.48      | r2_hidden(X0,sK3) != iProver_top
% 7.60/1.48      | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,[status(thm)],[c_4454,c_31]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12176,plain,
% 7.60/1.48      ( sK3 != k1_xboole_0
% 7.60/1.48      | sK6 = k1_xboole_0
% 7.60/1.48      | r2_hidden(X0,sK3) != iProver_top
% 7.60/1.48      | r2_hidden(k4_tarski(X0,sK1(sK6,X0)),sK6) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_12164,c_4672]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_101,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_103,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_101]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_781,plain,
% 7.60/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.60/1.48      | r2_hidden(X2,X0) != iProver_top
% 7.60/1.48      | r2_hidden(X2,X1) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2044,plain,
% 7.60/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.60/1.48      | r2_hidden(X0,X2) = iProver_top
% 7.60/1.48      | r1_tarski(X1,X2) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_780,c_781]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2940,plain,
% 7.60/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.60/1.48      | r2_hidden(sK0(X0,X2,X1),X3) = iProver_top
% 7.60/1.48      | r1_tarski(k1_relat_1(X1),X3) != iProver_top
% 7.60/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_774,c_2044]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8899,plain,
% 7.60/1.48      ( r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
% 7.60/1.48      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 7.60/1.48      | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
% 7.60/1.48      | v1_relat_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_2940,c_7202]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_9562,plain,
% 7.60/1.48      ( r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
% 7.60/1.48      | r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_8899,c_31,c_1049,c_1547]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_9563,plain,
% 7.60/1.48      ( r2_hidden(sK0(sK7,sK5,sK6),sK5) != iProver_top
% 7.60/1.48      | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_9562]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_9568,plain,
% 7.60/1.48      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 7.60/1.48      | r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
% 7.60/1.48      | v1_relat_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_776,c_9563]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_9778,plain,
% 7.60/1.48      ( r1_tarski(k1_relat_1(sK6),sK3) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_9568,c_31,c_1049,c_1547]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_9784,plain,
% 7.60/1.48      ( sK6 = k1_xboole_0
% 7.60/1.48      | r1_tarski(k1_relat_1(sK6),k1_xboole_0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_8143,c_9778]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12173,plain,
% 7.60/1.48      ( sK6 = k1_xboole_0 | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_12164,c_9784]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12337,plain,
% 7.60/1.48      ( sK6 = k1_xboole_0 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_12176,c_103,c_12173]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_16015,plain,
% 7.60/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.60/1.48      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.60/1.48      inference(light_normalisation,[status(thm)],[c_16012,c_12337]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_16552,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_16555,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_16552]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_16557,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_16555]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_17260,plain,
% 7.60/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_5461,c_2225,c_5472,c_6302,c_16015,c_16557]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12355,plain,
% 7.60/1.48      ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) != iProver_top ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_12337,c_9778]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_17272,plain,
% 7.60/1.48      ( r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.60/1.48      inference(demodulation,[status(thm)],[c_17260,c_12355]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_24179,plain,
% 7.60/1.48      ( $false ),
% 7.60/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_17272,c_782]) ).
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  ------                               Statistics
% 7.60/1.48  
% 7.60/1.48  ------ Selected
% 7.60/1.48  
% 7.60/1.48  total_time:                             0.706
% 7.60/1.48  
%------------------------------------------------------------------------------

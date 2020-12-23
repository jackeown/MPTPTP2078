%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:22 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 356 expanded)
%              Number of clauses        :   63 ( 113 expanded)
%              Number of leaves         :   20 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :  447 (1619 expanded)
%              Number of equality atoms :  113 ( 161 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ! [X3] :
            ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
          <=> ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
        <~> ? [X4] :
              ( r2_hidden(k4_tarski(X4,X3),X2)
              & m1_subset_1(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f41])).

fof(f45,plain,(
    ! [X2,X3,X1] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X5,X3),X2)
          & m1_subset_1(X5,X1) )
     => ( r2_hidden(k4_tarski(sK9,X3),X2)
        & m1_subset_1(sK9,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X4,sK8),X2)
              | ~ m1_subset_1(X4,X1) )
          | ~ r2_hidden(sK8,k2_relset_1(X1,X0,X2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,sK8),X2)
              & m1_subset_1(X5,X1) )
          | r2_hidden(sK8,k2_relset_1(X1,X0,X2)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                  | ~ m1_subset_1(X4,X1) )
              | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),X2)
                  & m1_subset_1(X5,X1) )
              | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),sK7)
                | ~ m1_subset_1(X4,sK6) )
            | ~ r2_hidden(X3,k2_relset_1(sK6,sK5,sK7)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),sK7)
                & m1_subset_1(X5,sK6) )
            | r2_hidden(X3,k2_relset_1(sK6,sK5,sK7)) ) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK8),sK7)
          | ~ m1_subset_1(X4,sK6) )
      | ~ r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) )
    & ( ( r2_hidden(k4_tarski(sK9,sK8),sK7)
        & m1_subset_1(sK9,sK6) )
      | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f42,f45,f44,f43])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK8),sK7)
      | ~ m1_subset_1(X4,sK6)
      | ~ r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7)
    | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f71,plain,
    ( m1_subset_1(sK9,sK6)
    | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1297,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1312,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2628,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1312])).

cnf(c_27,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1692,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_relat_1(k2_zfmisc_1(sK6,sK5))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_1693,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1692])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1760,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1761,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1760])).

cnf(c_2809,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2628,c_27,c_1693,c_1761])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1302,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2814,plain,
    ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2809,c_1302])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1303,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_309,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k3_xboole_0(X3,X2) = X3
    | k1_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_310,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_310])).

cnf(c_1296,plain,
    ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1767,plain,
    ( k3_xboole_0(k1_relat_1(sK7),sK6) = k1_relat_1(sK7)
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_1296])).

cnf(c_1981,plain,
    ( k3_xboole_0(k1_relat_1(sK7),sK6) = k1_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1767,c_27,c_1693,c_1761])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1315,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1984,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_1315])).

cnf(c_2461,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK7),sK6) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_1984])).

cnf(c_3845,plain,
    ( r2_hidden(sK4(X0,X1,sK7),sK6) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2461,c_27,c_1693,c_1761])).

cnf(c_3846,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK7),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_3845])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1313,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3853,plain,
    ( m1_subset_1(sK4(X0,X1,sK7),sK6) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3846,c_1313])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1304,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1301,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2386,plain,
    ( k2_relset_1(sK6,sK5,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1297,c_1301])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(X0,sK6)
    | ~ r2_hidden(k4_tarski(X0,sK8),sK7)
    | ~ r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1300,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
    | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2392,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
    | r2_hidden(sK8,k2_relat_1(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2386,c_1300])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7)
    | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1299,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1552,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1299,c_1300])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1644,plain,
    ( ~ r2_hidden(k4_tarski(sK9,sK8),sK7)
    | r2_hidden(sK8,k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1645,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7) != iProver_top
    | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1644])).

cnf(c_2448,plain,
    ( r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2392,c_1552,c_1645])).

cnf(c_2449,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_2448])).

cnf(c_2957,plain,
    ( m1_subset_1(sK4(sK8,X0,sK7),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1304,c_2449])).

cnf(c_3625,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | m1_subset_1(sK4(sK8,X0,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2957,c_27,c_1693,c_1761])).

cnf(c_3626,plain,
    ( m1_subset_1(sK4(sK8,X0,sK7),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3625])).

cnf(c_4834,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3853,c_3626])).

cnf(c_4840,plain,
    ( r2_hidden(sK8,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2814,c_4834])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK9,sK6)
    | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1298,plain,
    ( m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2391,plain,
    ( m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2386,c_1298])).

cnf(c_2390,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2386,c_1299])).

cnf(c_2816,plain,
    ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2391,c_1645,c_2390])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4840,c_2816])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.76/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.02  
% 2.76/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/1.02  
% 2.76/1.02  ------  iProver source info
% 2.76/1.02  
% 2.76/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.76/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/1.02  git: non_committed_changes: false
% 2.76/1.02  git: last_make_outside_of_git: false
% 2.76/1.02  
% 2.76/1.02  ------ 
% 2.76/1.02  
% 2.76/1.02  ------ Input Options
% 2.76/1.02  
% 2.76/1.02  --out_options                           all
% 2.76/1.02  --tptp_safe_out                         true
% 2.76/1.02  --problem_path                          ""
% 2.76/1.02  --include_path                          ""
% 2.76/1.02  --clausifier                            res/vclausify_rel
% 2.76/1.02  --clausifier_options                    --mode clausify
% 2.76/1.02  --stdin                                 false
% 2.76/1.02  --stats_out                             all
% 2.76/1.02  
% 2.76/1.02  ------ General Options
% 2.76/1.02  
% 2.76/1.02  --fof                                   false
% 2.76/1.02  --time_out_real                         305.
% 2.76/1.02  --time_out_virtual                      -1.
% 2.76/1.02  --symbol_type_check                     false
% 2.76/1.02  --clausify_out                          false
% 2.76/1.02  --sig_cnt_out                           false
% 2.76/1.02  --trig_cnt_out                          false
% 2.76/1.02  --trig_cnt_out_tolerance                1.
% 2.76/1.02  --trig_cnt_out_sk_spl                   false
% 2.76/1.02  --abstr_cl_out                          false
% 2.76/1.02  
% 2.76/1.02  ------ Global Options
% 2.76/1.02  
% 2.76/1.02  --schedule                              default
% 2.76/1.02  --add_important_lit                     false
% 2.76/1.02  --prop_solver_per_cl                    1000
% 2.76/1.02  --min_unsat_core                        false
% 2.76/1.02  --soft_assumptions                      false
% 2.76/1.02  --soft_lemma_size                       3
% 2.76/1.02  --prop_impl_unit_size                   0
% 2.76/1.02  --prop_impl_unit                        []
% 2.76/1.02  --share_sel_clauses                     true
% 2.76/1.02  --reset_solvers                         false
% 2.76/1.02  --bc_imp_inh                            [conj_cone]
% 2.76/1.02  --conj_cone_tolerance                   3.
% 2.76/1.02  --extra_neg_conj                        none
% 2.76/1.02  --large_theory_mode                     true
% 2.76/1.02  --prolific_symb_bound                   200
% 2.76/1.02  --lt_threshold                          2000
% 2.76/1.02  --clause_weak_htbl                      true
% 2.76/1.02  --gc_record_bc_elim                     false
% 2.76/1.02  
% 2.76/1.02  ------ Preprocessing Options
% 2.76/1.02  
% 2.76/1.02  --preprocessing_flag                    true
% 2.76/1.02  --time_out_prep_mult                    0.1
% 2.76/1.02  --splitting_mode                        input
% 2.76/1.02  --splitting_grd                         true
% 2.76/1.02  --splitting_cvd                         false
% 2.76/1.02  --splitting_cvd_svl                     false
% 2.76/1.02  --splitting_nvd                         32
% 2.76/1.02  --sub_typing                            true
% 2.76/1.02  --prep_gs_sim                           true
% 2.76/1.02  --prep_unflatten                        true
% 2.76/1.02  --prep_res_sim                          true
% 2.76/1.02  --prep_upred                            true
% 2.76/1.02  --prep_sem_filter                       exhaustive
% 2.76/1.02  --prep_sem_filter_out                   false
% 2.76/1.02  --pred_elim                             true
% 2.76/1.02  --res_sim_input                         true
% 2.76/1.02  --eq_ax_congr_red                       true
% 2.76/1.02  --pure_diseq_elim                       true
% 2.76/1.02  --brand_transform                       false
% 2.76/1.02  --non_eq_to_eq                          false
% 2.76/1.02  --prep_def_merge                        true
% 2.76/1.02  --prep_def_merge_prop_impl              false
% 2.76/1.02  --prep_def_merge_mbd                    true
% 2.76/1.02  --prep_def_merge_tr_red                 false
% 2.76/1.02  --prep_def_merge_tr_cl                  false
% 2.76/1.02  --smt_preprocessing                     true
% 2.76/1.02  --smt_ac_axioms                         fast
% 2.76/1.02  --preprocessed_out                      false
% 2.76/1.02  --preprocessed_stats                    false
% 2.76/1.02  
% 2.76/1.02  ------ Abstraction refinement Options
% 2.76/1.02  
% 2.76/1.02  --abstr_ref                             []
% 2.76/1.02  --abstr_ref_prep                        false
% 2.76/1.02  --abstr_ref_until_sat                   false
% 2.76/1.02  --abstr_ref_sig_restrict                funpre
% 2.76/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.02  --abstr_ref_under                       []
% 2.76/1.02  
% 2.76/1.02  ------ SAT Options
% 2.76/1.02  
% 2.76/1.02  --sat_mode                              false
% 2.76/1.02  --sat_fm_restart_options                ""
% 2.76/1.02  --sat_gr_def                            false
% 2.76/1.02  --sat_epr_types                         true
% 2.76/1.02  --sat_non_cyclic_types                  false
% 2.76/1.02  --sat_finite_models                     false
% 2.76/1.02  --sat_fm_lemmas                         false
% 2.76/1.02  --sat_fm_prep                           false
% 2.76/1.02  --sat_fm_uc_incr                        true
% 2.76/1.02  --sat_out_model                         small
% 2.76/1.02  --sat_out_clauses                       false
% 2.76/1.02  
% 2.76/1.02  ------ QBF Options
% 2.76/1.02  
% 2.76/1.02  --qbf_mode                              false
% 2.76/1.02  --qbf_elim_univ                         false
% 2.76/1.02  --qbf_dom_inst                          none
% 2.76/1.02  --qbf_dom_pre_inst                      false
% 2.76/1.02  --qbf_sk_in                             false
% 2.76/1.02  --qbf_pred_elim                         true
% 2.76/1.02  --qbf_split                             512
% 2.76/1.02  
% 2.76/1.02  ------ BMC1 Options
% 2.76/1.02  
% 2.76/1.02  --bmc1_incremental                      false
% 2.76/1.02  --bmc1_axioms                           reachable_all
% 2.76/1.02  --bmc1_min_bound                        0
% 2.76/1.02  --bmc1_max_bound                        -1
% 2.76/1.02  --bmc1_max_bound_default                -1
% 2.76/1.02  --bmc1_symbol_reachability              true
% 2.76/1.02  --bmc1_property_lemmas                  false
% 2.76/1.02  --bmc1_k_induction                      false
% 2.76/1.02  --bmc1_non_equiv_states                 false
% 2.76/1.02  --bmc1_deadlock                         false
% 2.76/1.02  --bmc1_ucm                              false
% 2.76/1.02  --bmc1_add_unsat_core                   none
% 2.76/1.02  --bmc1_unsat_core_children              false
% 2.76/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.02  --bmc1_out_stat                         full
% 2.76/1.02  --bmc1_ground_init                      false
% 2.76/1.02  --bmc1_pre_inst_next_state              false
% 2.76/1.02  --bmc1_pre_inst_state                   false
% 2.76/1.02  --bmc1_pre_inst_reach_state             false
% 2.76/1.02  --bmc1_out_unsat_core                   false
% 2.76/1.02  --bmc1_aig_witness_out                  false
% 2.76/1.02  --bmc1_verbose                          false
% 2.76/1.02  --bmc1_dump_clauses_tptp                false
% 2.76/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.02  --bmc1_dump_file                        -
% 2.76/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.02  --bmc1_ucm_extend_mode                  1
% 2.76/1.02  --bmc1_ucm_init_mode                    2
% 2.76/1.02  --bmc1_ucm_cone_mode                    none
% 2.76/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.02  --bmc1_ucm_relax_model                  4
% 2.76/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.02  --bmc1_ucm_layered_model                none
% 2.76/1.02  --bmc1_ucm_max_lemma_size               10
% 2.76/1.02  
% 2.76/1.02  ------ AIG Options
% 2.76/1.02  
% 2.76/1.02  --aig_mode                              false
% 2.76/1.02  
% 2.76/1.02  ------ Instantiation Options
% 2.76/1.02  
% 2.76/1.02  --instantiation_flag                    true
% 2.76/1.02  --inst_sos_flag                         false
% 2.76/1.02  --inst_sos_phase                        true
% 2.76/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.02  --inst_lit_sel_side                     num_symb
% 2.76/1.02  --inst_solver_per_active                1400
% 2.76/1.02  --inst_solver_calls_frac                1.
% 2.76/1.02  --inst_passive_queue_type               priority_queues
% 2.76/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.02  --inst_passive_queues_freq              [25;2]
% 2.76/1.02  --inst_dismatching                      true
% 2.76/1.02  --inst_eager_unprocessed_to_passive     true
% 2.76/1.02  --inst_prop_sim_given                   true
% 2.76/1.02  --inst_prop_sim_new                     false
% 2.76/1.02  --inst_subs_new                         false
% 2.76/1.02  --inst_eq_res_simp                      false
% 2.76/1.02  --inst_subs_given                       false
% 2.76/1.02  --inst_orphan_elimination               true
% 2.76/1.02  --inst_learning_loop_flag               true
% 2.76/1.02  --inst_learning_start                   3000
% 2.76/1.02  --inst_learning_factor                  2
% 2.76/1.02  --inst_start_prop_sim_after_learn       3
% 2.76/1.02  --inst_sel_renew                        solver
% 2.76/1.02  --inst_lit_activity_flag                true
% 2.76/1.02  --inst_restr_to_given                   false
% 2.76/1.02  --inst_activity_threshold               500
% 2.76/1.02  --inst_out_proof                        true
% 2.76/1.02  
% 2.76/1.02  ------ Resolution Options
% 2.76/1.02  
% 2.76/1.02  --resolution_flag                       true
% 2.76/1.02  --res_lit_sel                           adaptive
% 2.76/1.02  --res_lit_sel_side                      none
% 2.76/1.02  --res_ordering                          kbo
% 2.76/1.02  --res_to_prop_solver                    active
% 2.76/1.02  --res_prop_simpl_new                    false
% 2.76/1.02  --res_prop_simpl_given                  true
% 2.76/1.02  --res_passive_queue_type                priority_queues
% 2.76/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.02  --res_passive_queues_freq               [15;5]
% 2.76/1.02  --res_forward_subs                      full
% 2.76/1.02  --res_backward_subs                     full
% 2.76/1.02  --res_forward_subs_resolution           true
% 2.76/1.02  --res_backward_subs_resolution          true
% 2.76/1.02  --res_orphan_elimination                true
% 2.76/1.02  --res_time_limit                        2.
% 2.76/1.02  --res_out_proof                         true
% 2.76/1.02  
% 2.76/1.02  ------ Superposition Options
% 2.76/1.02  
% 2.76/1.02  --superposition_flag                    true
% 2.76/1.02  --sup_passive_queue_type                priority_queues
% 2.76/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.02  --demod_completeness_check              fast
% 2.76/1.02  --demod_use_ground                      true
% 2.76/1.02  --sup_to_prop_solver                    passive
% 2.76/1.02  --sup_prop_simpl_new                    true
% 2.76/1.02  --sup_prop_simpl_given                  true
% 2.76/1.02  --sup_fun_splitting                     false
% 2.76/1.02  --sup_smt_interval                      50000
% 2.76/1.02  
% 2.76/1.02  ------ Superposition Simplification Setup
% 2.76/1.02  
% 2.76/1.02  --sup_indices_passive                   []
% 2.76/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.02  --sup_full_bw                           [BwDemod]
% 2.76/1.02  --sup_immed_triv                        [TrivRules]
% 2.76/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.02  --sup_immed_bw_main                     []
% 2.76/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.02  
% 2.76/1.02  ------ Combination Options
% 2.76/1.02  
% 2.76/1.02  --comb_res_mult                         3
% 2.76/1.02  --comb_sup_mult                         2
% 2.76/1.02  --comb_inst_mult                        10
% 2.76/1.02  
% 2.76/1.02  ------ Debug Options
% 2.76/1.02  
% 2.76/1.02  --dbg_backtrace                         false
% 2.76/1.02  --dbg_dump_prop_clauses                 false
% 2.76/1.02  --dbg_dump_prop_clauses_file            -
% 2.76/1.02  --dbg_out_stat                          false
% 2.76/1.02  ------ Parsing...
% 2.76/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/1.02  
% 2.76/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.76/1.02  
% 2.76/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/1.02  
% 2.76/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/1.02  ------ Proving...
% 2.76/1.02  ------ Problem Properties 
% 2.76/1.02  
% 2.76/1.02  
% 2.76/1.02  clauses                                 24
% 2.76/1.02  conjectures                             4
% 2.76/1.02  EPR                                     1
% 2.76/1.02  Horn                                    19
% 2.76/1.02  unary                                   2
% 2.76/1.02  binary                                  9
% 2.76/1.02  lits                                    62
% 2.76/1.02  lits eq                                 8
% 2.76/1.02  fd_pure                                 0
% 2.76/1.02  fd_pseudo                               0
% 2.76/1.02  fd_cond                                 0
% 2.76/1.02  fd_pseudo_cond                          5
% 2.76/1.02  AC symbols                              0
% 2.76/1.02  
% 2.76/1.02  ------ Schedule dynamic 5 is on 
% 2.76/1.02  
% 2.76/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/1.02  
% 2.76/1.02  
% 2.76/1.02  ------ 
% 2.76/1.02  Current options:
% 2.76/1.02  ------ 
% 2.76/1.02  
% 2.76/1.02  ------ Input Options
% 2.76/1.02  
% 2.76/1.02  --out_options                           all
% 2.76/1.02  --tptp_safe_out                         true
% 2.76/1.02  --problem_path                          ""
% 2.76/1.02  --include_path                          ""
% 2.76/1.02  --clausifier                            res/vclausify_rel
% 2.76/1.02  --clausifier_options                    --mode clausify
% 2.76/1.02  --stdin                                 false
% 2.76/1.02  --stats_out                             all
% 2.76/1.02  
% 2.76/1.02  ------ General Options
% 2.76/1.02  
% 2.76/1.02  --fof                                   false
% 2.76/1.02  --time_out_real                         305.
% 2.76/1.02  --time_out_virtual                      -1.
% 2.76/1.02  --symbol_type_check                     false
% 2.76/1.02  --clausify_out                          false
% 2.76/1.02  --sig_cnt_out                           false
% 2.76/1.02  --trig_cnt_out                          false
% 2.76/1.02  --trig_cnt_out_tolerance                1.
% 2.76/1.02  --trig_cnt_out_sk_spl                   false
% 2.76/1.02  --abstr_cl_out                          false
% 2.76/1.02  
% 2.76/1.02  ------ Global Options
% 2.76/1.02  
% 2.76/1.02  --schedule                              default
% 2.76/1.02  --add_important_lit                     false
% 2.76/1.02  --prop_solver_per_cl                    1000
% 2.76/1.02  --min_unsat_core                        false
% 2.76/1.02  --soft_assumptions                      false
% 2.76/1.02  --soft_lemma_size                       3
% 2.76/1.02  --prop_impl_unit_size                   0
% 2.76/1.02  --prop_impl_unit                        []
% 2.76/1.02  --share_sel_clauses                     true
% 2.76/1.02  --reset_solvers                         false
% 2.76/1.02  --bc_imp_inh                            [conj_cone]
% 2.76/1.02  --conj_cone_tolerance                   3.
% 2.76/1.02  --extra_neg_conj                        none
% 2.76/1.02  --large_theory_mode                     true
% 2.76/1.02  --prolific_symb_bound                   200
% 2.76/1.02  --lt_threshold                          2000
% 2.76/1.02  --clause_weak_htbl                      true
% 2.76/1.02  --gc_record_bc_elim                     false
% 2.76/1.02  
% 2.76/1.02  ------ Preprocessing Options
% 2.76/1.02  
% 2.76/1.02  --preprocessing_flag                    true
% 2.76/1.02  --time_out_prep_mult                    0.1
% 2.76/1.02  --splitting_mode                        input
% 2.76/1.02  --splitting_grd                         true
% 2.76/1.02  --splitting_cvd                         false
% 2.76/1.02  --splitting_cvd_svl                     false
% 2.76/1.02  --splitting_nvd                         32
% 2.76/1.02  --sub_typing                            true
% 2.76/1.02  --prep_gs_sim                           true
% 2.76/1.02  --prep_unflatten                        true
% 2.76/1.02  --prep_res_sim                          true
% 2.76/1.02  --prep_upred                            true
% 2.76/1.02  --prep_sem_filter                       exhaustive
% 2.76/1.02  --prep_sem_filter_out                   false
% 2.76/1.02  --pred_elim                             true
% 2.76/1.02  --res_sim_input                         true
% 2.76/1.02  --eq_ax_congr_red                       true
% 2.76/1.02  --pure_diseq_elim                       true
% 2.76/1.02  --brand_transform                       false
% 2.76/1.02  --non_eq_to_eq                          false
% 2.76/1.02  --prep_def_merge                        true
% 2.76/1.02  --prep_def_merge_prop_impl              false
% 2.76/1.02  --prep_def_merge_mbd                    true
% 2.76/1.02  --prep_def_merge_tr_red                 false
% 2.76/1.02  --prep_def_merge_tr_cl                  false
% 2.76/1.02  --smt_preprocessing                     true
% 2.76/1.02  --smt_ac_axioms                         fast
% 2.76/1.02  --preprocessed_out                      false
% 2.76/1.02  --preprocessed_stats                    false
% 2.76/1.02  
% 2.76/1.02  ------ Abstraction refinement Options
% 2.76/1.02  
% 2.76/1.02  --abstr_ref                             []
% 2.76/1.02  --abstr_ref_prep                        false
% 2.76/1.02  --abstr_ref_until_sat                   false
% 2.76/1.02  --abstr_ref_sig_restrict                funpre
% 2.76/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.02  --abstr_ref_under                       []
% 2.76/1.02  
% 2.76/1.02  ------ SAT Options
% 2.76/1.02  
% 2.76/1.02  --sat_mode                              false
% 2.76/1.02  --sat_fm_restart_options                ""
% 2.76/1.02  --sat_gr_def                            false
% 2.76/1.02  --sat_epr_types                         true
% 2.76/1.02  --sat_non_cyclic_types                  false
% 2.76/1.02  --sat_finite_models                     false
% 2.76/1.02  --sat_fm_lemmas                         false
% 2.76/1.02  --sat_fm_prep                           false
% 2.76/1.02  --sat_fm_uc_incr                        true
% 2.76/1.02  --sat_out_model                         small
% 2.76/1.02  --sat_out_clauses                       false
% 2.76/1.02  
% 2.76/1.02  ------ QBF Options
% 2.76/1.02  
% 2.76/1.02  --qbf_mode                              false
% 2.76/1.02  --qbf_elim_univ                         false
% 2.76/1.02  --qbf_dom_inst                          none
% 2.76/1.02  --qbf_dom_pre_inst                      false
% 2.76/1.02  --qbf_sk_in                             false
% 2.76/1.02  --qbf_pred_elim                         true
% 2.76/1.02  --qbf_split                             512
% 2.76/1.02  
% 2.76/1.02  ------ BMC1 Options
% 2.76/1.02  
% 2.76/1.02  --bmc1_incremental                      false
% 2.76/1.02  --bmc1_axioms                           reachable_all
% 2.76/1.02  --bmc1_min_bound                        0
% 2.76/1.02  --bmc1_max_bound                        -1
% 2.76/1.02  --bmc1_max_bound_default                -1
% 2.76/1.02  --bmc1_symbol_reachability              true
% 2.76/1.02  --bmc1_property_lemmas                  false
% 2.76/1.02  --bmc1_k_induction                      false
% 2.76/1.02  --bmc1_non_equiv_states                 false
% 2.76/1.02  --bmc1_deadlock                         false
% 2.76/1.02  --bmc1_ucm                              false
% 2.76/1.02  --bmc1_add_unsat_core                   none
% 2.76/1.02  --bmc1_unsat_core_children              false
% 2.76/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.02  --bmc1_out_stat                         full
% 2.76/1.02  --bmc1_ground_init                      false
% 2.76/1.02  --bmc1_pre_inst_next_state              false
% 2.76/1.02  --bmc1_pre_inst_state                   false
% 2.76/1.02  --bmc1_pre_inst_reach_state             false
% 2.76/1.02  --bmc1_out_unsat_core                   false
% 2.76/1.02  --bmc1_aig_witness_out                  false
% 2.76/1.02  --bmc1_verbose                          false
% 2.76/1.02  --bmc1_dump_clauses_tptp                false
% 2.76/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.02  --bmc1_dump_file                        -
% 2.76/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.02  --bmc1_ucm_extend_mode                  1
% 2.76/1.02  --bmc1_ucm_init_mode                    2
% 2.76/1.02  --bmc1_ucm_cone_mode                    none
% 2.76/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.02  --bmc1_ucm_relax_model                  4
% 2.76/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.02  --bmc1_ucm_layered_model                none
% 2.76/1.02  --bmc1_ucm_max_lemma_size               10
% 2.76/1.02  
% 2.76/1.02  ------ AIG Options
% 2.76/1.02  
% 2.76/1.02  --aig_mode                              false
% 2.76/1.02  
% 2.76/1.02  ------ Instantiation Options
% 2.76/1.02  
% 2.76/1.02  --instantiation_flag                    true
% 2.76/1.02  --inst_sos_flag                         false
% 2.76/1.02  --inst_sos_phase                        true
% 2.76/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.02  --inst_lit_sel_side                     none
% 2.76/1.02  --inst_solver_per_active                1400
% 2.76/1.02  --inst_solver_calls_frac                1.
% 2.76/1.02  --inst_passive_queue_type               priority_queues
% 2.76/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.02  --inst_passive_queues_freq              [25;2]
% 2.76/1.02  --inst_dismatching                      true
% 2.76/1.02  --inst_eager_unprocessed_to_passive     true
% 2.76/1.02  --inst_prop_sim_given                   true
% 2.76/1.02  --inst_prop_sim_new                     false
% 2.76/1.02  --inst_subs_new                         false
% 2.76/1.02  --inst_eq_res_simp                      false
% 2.76/1.02  --inst_subs_given                       false
% 2.76/1.02  --inst_orphan_elimination               true
% 2.76/1.02  --inst_learning_loop_flag               true
% 2.76/1.02  --inst_learning_start                   3000
% 2.76/1.02  --inst_learning_factor                  2
% 2.76/1.02  --inst_start_prop_sim_after_learn       3
% 2.76/1.02  --inst_sel_renew                        solver
% 2.76/1.02  --inst_lit_activity_flag                true
% 2.76/1.02  --inst_restr_to_given                   false
% 2.76/1.02  --inst_activity_threshold               500
% 2.76/1.02  --inst_out_proof                        true
% 2.76/1.02  
% 2.76/1.02  ------ Resolution Options
% 2.76/1.02  
% 2.76/1.02  --resolution_flag                       false
% 2.76/1.02  --res_lit_sel                           adaptive
% 2.76/1.02  --res_lit_sel_side                      none
% 2.76/1.02  --res_ordering                          kbo
% 2.76/1.02  --res_to_prop_solver                    active
% 2.76/1.02  --res_prop_simpl_new                    false
% 2.76/1.02  --res_prop_simpl_given                  true
% 2.76/1.02  --res_passive_queue_type                priority_queues
% 2.76/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.02  --res_passive_queues_freq               [15;5]
% 2.76/1.02  --res_forward_subs                      full
% 2.76/1.02  --res_backward_subs                     full
% 2.76/1.02  --res_forward_subs_resolution           true
% 2.76/1.02  --res_backward_subs_resolution          true
% 2.76/1.02  --res_orphan_elimination                true
% 2.76/1.02  --res_time_limit                        2.
% 2.76/1.02  --res_out_proof                         true
% 2.76/1.02  
% 2.76/1.02  ------ Superposition Options
% 2.76/1.02  
% 2.76/1.02  --superposition_flag                    true
% 2.76/1.02  --sup_passive_queue_type                priority_queues
% 2.76/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.02  --demod_completeness_check              fast
% 2.76/1.03  --demod_use_ground                      true
% 2.76/1.03  --sup_to_prop_solver                    passive
% 2.76/1.03  --sup_prop_simpl_new                    true
% 2.76/1.03  --sup_prop_simpl_given                  true
% 2.76/1.03  --sup_fun_splitting                     false
% 2.76/1.03  --sup_smt_interval                      50000
% 2.76/1.03  
% 2.76/1.03  ------ Superposition Simplification Setup
% 2.76/1.03  
% 2.76/1.03  --sup_indices_passive                   []
% 2.76/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.03  --sup_full_bw                           [BwDemod]
% 2.76/1.03  --sup_immed_triv                        [TrivRules]
% 2.76/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.03  --sup_immed_bw_main                     []
% 2.76/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.03  
% 2.76/1.03  ------ Combination Options
% 2.76/1.03  
% 2.76/1.03  --comb_res_mult                         3
% 2.76/1.03  --comb_sup_mult                         2
% 2.76/1.03  --comb_inst_mult                        10
% 2.76/1.03  
% 2.76/1.03  ------ Debug Options
% 2.76/1.03  
% 2.76/1.03  --dbg_backtrace                         false
% 2.76/1.03  --dbg_dump_prop_clauses                 false
% 2.76/1.03  --dbg_dump_prop_clauses_file            -
% 2.76/1.03  --dbg_out_stat                          false
% 2.76/1.03  
% 2.76/1.03  
% 2.76/1.03  
% 2.76/1.03  
% 2.76/1.03  ------ Proving...
% 2.76/1.03  
% 2.76/1.03  
% 2.76/1.03  % SZS status Theorem for theBenchmark.p
% 2.76/1.03  
% 2.76/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/1.03  
% 2.76/1.03  fof(f12,conjecture,(
% 2.76/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f13,negated_conjecture,(
% 2.76/1.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 2.76/1.03    inference(negated_conjecture,[],[f12])).
% 2.76/1.03  
% 2.76/1.03  fof(f14,plain,(
% 2.76/1.03    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))),
% 2.76/1.03    inference(pure_predicate_removal,[],[f13])).
% 2.76/1.03  
% 2.76/1.03  fof(f24,plain,(
% 2.76/1.03    ? [X0,X1,X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.76/1.03    inference(ennf_transformation,[],[f14])).
% 2.76/1.03  
% 2.76/1.03  fof(f41,plain,(
% 2.76/1.03    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.76/1.03    inference(nnf_transformation,[],[f24])).
% 2.76/1.03  
% 2.76/1.03  fof(f42,plain,(
% 2.76/1.03    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.76/1.03    inference(rectify,[],[f41])).
% 2.76/1.03  
% 2.76/1.03  fof(f45,plain,(
% 2.76/1.03    ( ! [X2,X3,X1] : (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) => (r2_hidden(k4_tarski(sK9,X3),X2) & m1_subset_1(sK9,X1))) )),
% 2.76/1.03    introduced(choice_axiom,[])).
% 2.76/1.03  
% 2.76/1.03  fof(f44,plain,(
% 2.76/1.03    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK8),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(sK8,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK8),X2) & m1_subset_1(X5,X1)) | r2_hidden(sK8,k2_relset_1(X1,X0,X2))))) )),
% 2.76/1.03    introduced(choice_axiom,[])).
% 2.76/1.03  
% 2.76/1.03  fof(f43,plain,(
% 2.76/1.03    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK7) | ~m1_subset_1(X4,sK6)) | ~r2_hidden(X3,k2_relset_1(sK6,sK5,sK7))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK7) & m1_subset_1(X5,sK6)) | r2_hidden(X3,k2_relset_1(sK6,sK5,sK7)))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))))),
% 2.76/1.03    introduced(choice_axiom,[])).
% 2.76/1.03  
% 2.76/1.03  fof(f46,plain,(
% 2.76/1.03    ((! [X4] : (~r2_hidden(k4_tarski(X4,sK8),sK7) | ~m1_subset_1(X4,sK6)) | ~r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7))) & ((r2_hidden(k4_tarski(sK9,sK8),sK7) & m1_subset_1(sK9,sK6)) | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 2.76/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f42,f45,f44,f43])).
% 2.76/1.03  
% 2.76/1.03  fof(f70,plain,(
% 2.76/1.03    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 2.76/1.03    inference(cnf_transformation,[],[f46])).
% 2.76/1.03  
% 2.76/1.03  fof(f4,axiom,(
% 2.76/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f18,plain,(
% 2.76/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.76/1.03    inference(ennf_transformation,[],[f4])).
% 2.76/1.03  
% 2.76/1.03  fof(f55,plain,(
% 2.76/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.76/1.03    inference(cnf_transformation,[],[f18])).
% 2.76/1.03  
% 2.76/1.03  fof(f7,axiom,(
% 2.76/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f62,plain,(
% 2.76/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.76/1.03    inference(cnf_transformation,[],[f7])).
% 2.76/1.03  
% 2.76/1.03  fof(f9,axiom,(
% 2.76/1.03    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f21,plain,(
% 2.76/1.03    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.76/1.03    inference(ennf_transformation,[],[f9])).
% 2.76/1.03  
% 2.76/1.03  fof(f67,plain,(
% 2.76/1.03    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.76/1.03    inference(cnf_transformation,[],[f21])).
% 2.76/1.03  
% 2.76/1.03  fof(f8,axiom,(
% 2.76/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f20,plain,(
% 2.76/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.76/1.03    inference(ennf_transformation,[],[f8])).
% 2.76/1.03  
% 2.76/1.03  fof(f37,plain,(
% 2.76/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.76/1.03    inference(nnf_transformation,[],[f20])).
% 2.76/1.03  
% 2.76/1.03  fof(f38,plain,(
% 2.76/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.76/1.03    inference(rectify,[],[f37])).
% 2.76/1.03  
% 2.76/1.03  fof(f39,plain,(
% 2.76/1.03    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 2.76/1.03    introduced(choice_axiom,[])).
% 2.76/1.03  
% 2.76/1.03  fof(f40,plain,(
% 2.76/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.76/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 2.76/1.03  
% 2.76/1.03  fof(f63,plain,(
% 2.76/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.76/1.03    inference(cnf_transformation,[],[f40])).
% 2.76/1.03  
% 2.76/1.03  fof(f10,axiom,(
% 2.76/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f15,plain,(
% 2.76/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.76/1.03    inference(pure_predicate_removal,[],[f10])).
% 2.76/1.03  
% 2.76/1.03  fof(f22,plain,(
% 2.76/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.03    inference(ennf_transformation,[],[f15])).
% 2.76/1.03  
% 2.76/1.03  fof(f68,plain,(
% 2.76/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.03    inference(cnf_transformation,[],[f22])).
% 2.76/1.03  
% 2.76/1.03  fof(f2,axiom,(
% 2.76/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f16,plain,(
% 2.76/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.76/1.03    inference(ennf_transformation,[],[f2])).
% 2.76/1.03  
% 2.76/1.03  fof(f53,plain,(
% 2.76/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.76/1.03    inference(cnf_transformation,[],[f16])).
% 2.76/1.03  
% 2.76/1.03  fof(f5,axiom,(
% 2.76/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f19,plain,(
% 2.76/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.76/1.03    inference(ennf_transformation,[],[f5])).
% 2.76/1.03  
% 2.76/1.03  fof(f30,plain,(
% 2.76/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.76/1.03    inference(nnf_transformation,[],[f19])).
% 2.76/1.03  
% 2.76/1.03  fof(f56,plain,(
% 2.76/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.76/1.03    inference(cnf_transformation,[],[f30])).
% 2.76/1.03  
% 2.76/1.03  fof(f1,axiom,(
% 2.76/1.03    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f25,plain,(
% 2.76/1.03    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.76/1.03    inference(nnf_transformation,[],[f1])).
% 2.76/1.03  
% 2.76/1.03  fof(f26,plain,(
% 2.76/1.03    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.76/1.03    inference(flattening,[],[f25])).
% 2.76/1.03  
% 2.76/1.03  fof(f27,plain,(
% 2.76/1.03    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.76/1.03    inference(rectify,[],[f26])).
% 2.76/1.03  
% 2.76/1.03  fof(f28,plain,(
% 2.76/1.03    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.76/1.03    introduced(choice_axiom,[])).
% 2.76/1.03  
% 2.76/1.03  fof(f29,plain,(
% 2.76/1.03    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.76/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.76/1.03  
% 2.76/1.03  fof(f48,plain,(
% 2.76/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.76/1.03    inference(cnf_transformation,[],[f29])).
% 2.76/1.03  
% 2.76/1.03  fof(f75,plain,(
% 2.76/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.76/1.03    inference(equality_resolution,[],[f48])).
% 2.76/1.03  
% 2.76/1.03  fof(f3,axiom,(
% 2.76/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f17,plain,(
% 2.76/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.76/1.03    inference(ennf_transformation,[],[f3])).
% 2.76/1.03  
% 2.76/1.03  fof(f54,plain,(
% 2.76/1.03    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.76/1.03    inference(cnf_transformation,[],[f17])).
% 2.76/1.03  
% 2.76/1.03  fof(f64,plain,(
% 2.76/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.76/1.03    inference(cnf_transformation,[],[f40])).
% 2.76/1.03  
% 2.76/1.03  fof(f11,axiom,(
% 2.76/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f23,plain,(
% 2.76/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.03    inference(ennf_transformation,[],[f11])).
% 2.76/1.03  
% 2.76/1.03  fof(f69,plain,(
% 2.76/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.03    inference(cnf_transformation,[],[f23])).
% 2.76/1.03  
% 2.76/1.03  fof(f73,plain,(
% 2.76/1.03    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK8),sK7) | ~m1_subset_1(X4,sK6) | ~r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7))) )),
% 2.76/1.03    inference(cnf_transformation,[],[f46])).
% 2.76/1.03  
% 2.76/1.03  fof(f72,plain,(
% 2.76/1.03    r2_hidden(k4_tarski(sK9,sK8),sK7) | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7))),
% 2.76/1.03    inference(cnf_transformation,[],[f46])).
% 2.76/1.03  
% 2.76/1.03  fof(f6,axiom,(
% 2.76/1.03    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.76/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/1.03  
% 2.76/1.03  fof(f31,plain,(
% 2.76/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 2.76/1.03    inference(nnf_transformation,[],[f6])).
% 2.76/1.03  
% 2.76/1.03  fof(f32,plain,(
% 2.76/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.76/1.03    inference(rectify,[],[f31])).
% 2.76/1.03  
% 2.76/1.03  fof(f35,plain,(
% 2.76/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 2.76/1.03    introduced(choice_axiom,[])).
% 2.76/1.03  
% 2.76/1.03  fof(f34,plain,(
% 2.76/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 2.76/1.03    introduced(choice_axiom,[])).
% 2.76/1.03  
% 2.76/1.03  fof(f33,plain,(
% 2.76/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.76/1.03    introduced(choice_axiom,[])).
% 2.76/1.03  
% 2.76/1.03  fof(f36,plain,(
% 2.76/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.76/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).
% 2.76/1.03  
% 2.76/1.03  fof(f59,plain,(
% 2.76/1.03    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 2.76/1.03    inference(cnf_transformation,[],[f36])).
% 2.76/1.03  
% 2.76/1.03  fof(f77,plain,(
% 2.76/1.03    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 2.76/1.03    inference(equality_resolution,[],[f59])).
% 2.76/1.03  
% 2.76/1.03  fof(f71,plain,(
% 2.76/1.03    m1_subset_1(sK9,sK6) | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7))),
% 2.76/1.03    inference(cnf_transformation,[],[f46])).
% 2.76/1.03  
% 2.76/1.03  cnf(c_26,negated_conjecture,
% 2.76/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
% 2.76/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1297,plain,
% 2.76/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_8,plain,
% 2.76/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/1.03      | ~ v1_relat_1(X1)
% 2.76/1.03      | v1_relat_1(X0) ),
% 2.76/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1312,plain,
% 2.76/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.76/1.03      | v1_relat_1(X1) != iProver_top
% 2.76/1.03      | v1_relat_1(X0) = iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2628,plain,
% 2.76/1.03      ( v1_relat_1(k2_zfmisc_1(sK6,sK5)) != iProver_top
% 2.76/1.03      | v1_relat_1(sK7) = iProver_top ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_1297,c_1312]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_27,plain,
% 2.76/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1498,plain,
% 2.76/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.03      | v1_relat_1(X0)
% 2.76/1.03      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.76/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1692,plain,
% 2.76/1.03      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.76/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK6,sK5))
% 2.76/1.03      | v1_relat_1(sK7) ),
% 2.76/1.03      inference(instantiation,[status(thm)],[c_1498]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1693,plain,
% 2.76/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.76/1.03      | v1_relat_1(k2_zfmisc_1(sK6,sK5)) != iProver_top
% 2.76/1.03      | v1_relat_1(sK7) = iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_1692]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_15,plain,
% 2.76/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.76/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1760,plain,
% 2.76/1.03      ( v1_relat_1(k2_zfmisc_1(sK6,sK5)) ),
% 2.76/1.03      inference(instantiation,[status(thm)],[c_15]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1761,plain,
% 2.76/1.03      ( v1_relat_1(k2_zfmisc_1(sK6,sK5)) = iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_1760]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2809,plain,
% 2.76/1.03      ( v1_relat_1(sK7) = iProver_top ),
% 2.76/1.03      inference(global_propositional_subsumption,
% 2.76/1.03                [status(thm)],
% 2.76/1.03                [c_2628,c_27,c_1693,c_1761]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_20,plain,
% 2.76/1.03      ( ~ v1_relat_1(X0)
% 2.76/1.03      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.76/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1302,plain,
% 2.76/1.03      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.76/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2814,plain,
% 2.76/1.03      ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7) ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_2809,c_1302]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_19,plain,
% 2.76/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.76/1.03      | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
% 2.76/1.03      | ~ v1_relat_1(X1) ),
% 2.76/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1303,plain,
% 2.76/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.76/1.03      | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.76/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_21,plain,
% 2.76/1.03      ( v4_relat_1(X0,X1)
% 2.76/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.76/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_6,plain,
% 2.76/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.76/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_10,plain,
% 2.76/1.03      ( ~ v4_relat_1(X0,X1)
% 2.76/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 2.76/1.03      | ~ v1_relat_1(X0) ),
% 2.76/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_309,plain,
% 2.76/1.03      ( ~ v4_relat_1(X0,X1)
% 2.76/1.03      | ~ v1_relat_1(X0)
% 2.76/1.03      | X1 != X2
% 2.76/1.03      | k3_xboole_0(X3,X2) = X3
% 2.76/1.03      | k1_relat_1(X0) != X3 ),
% 2.76/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_310,plain,
% 2.76/1.03      ( ~ v4_relat_1(X0,X1)
% 2.76/1.03      | ~ v1_relat_1(X0)
% 2.76/1.03      | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(X0) ),
% 2.76/1.03      inference(unflattening,[status(thm)],[c_309]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_328,plain,
% 2.76/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.03      | ~ v1_relat_1(X0)
% 2.76/1.03      | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(X0) ),
% 2.76/1.03      inference(resolution,[status(thm)],[c_21,c_310]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1296,plain,
% 2.76/1.03      ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(X0)
% 2.76/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.76/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1767,plain,
% 2.76/1.03      ( k3_xboole_0(k1_relat_1(sK7),sK6) = k1_relat_1(sK7)
% 2.76/1.03      | v1_relat_1(sK7) != iProver_top ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_1297,c_1296]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1981,plain,
% 2.76/1.03      ( k3_xboole_0(k1_relat_1(sK7),sK6) = k1_relat_1(sK7) ),
% 2.76/1.03      inference(global_propositional_subsumption,
% 2.76/1.03                [status(thm)],
% 2.76/1.03                [c_1767,c_27,c_1693,c_1761]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_4,plain,
% 2.76/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.76/1.03      inference(cnf_transformation,[],[f75]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1315,plain,
% 2.76/1.03      ( r2_hidden(X0,X1) = iProver_top
% 2.76/1.03      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1984,plain,
% 2.76/1.03      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.76/1.03      | r2_hidden(X0,sK6) = iProver_top ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_1981,c_1315]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2461,plain,
% 2.76/1.03      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.76/1.03      | r2_hidden(sK4(X0,X1,sK7),sK6) = iProver_top
% 2.76/1.03      | v1_relat_1(sK7) != iProver_top ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_1303,c_1984]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_3845,plain,
% 2.76/1.03      ( r2_hidden(sK4(X0,X1,sK7),sK6) = iProver_top
% 2.76/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 2.76/1.03      inference(global_propositional_subsumption,
% 2.76/1.03                [status(thm)],
% 2.76/1.03                [c_2461,c_27,c_1693,c_1761]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_3846,plain,
% 2.76/1.03      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.76/1.03      | r2_hidden(sK4(X0,X1,sK7),sK6) = iProver_top ),
% 2.76/1.03      inference(renaming,[status(thm)],[c_3845]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_7,plain,
% 2.76/1.03      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.76/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1313,plain,
% 2.76/1.03      ( m1_subset_1(X0,X1) = iProver_top
% 2.76/1.03      | r2_hidden(X0,X1) != iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_3853,plain,
% 2.76/1.03      ( m1_subset_1(sK4(X0,X1,sK7),sK6) = iProver_top
% 2.76/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_3846,c_1313]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_18,plain,
% 2.76/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.76/1.03      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
% 2.76/1.03      | ~ v1_relat_1(X1) ),
% 2.76/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1304,plain,
% 2.76/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.76/1.03      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1) = iProver_top
% 2.76/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_22,plain,
% 2.76/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.76/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1301,plain,
% 2.76/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.76/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2386,plain,
% 2.76/1.03      ( k2_relset_1(sK6,sK5,sK7) = k2_relat_1(sK7) ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_1297,c_1301]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_23,negated_conjecture,
% 2.76/1.03      ( ~ m1_subset_1(X0,sK6)
% 2.76/1.03      | ~ r2_hidden(k4_tarski(X0,sK8),sK7)
% 2.76/1.03      | ~ r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) ),
% 2.76/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1300,plain,
% 2.76/1.03      ( m1_subset_1(X0,sK6) != iProver_top
% 2.76/1.03      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
% 2.76/1.03      | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) != iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2392,plain,
% 2.76/1.03      ( m1_subset_1(X0,sK6) != iProver_top
% 2.76/1.03      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
% 2.76/1.03      | r2_hidden(sK8,k2_relat_1(sK7)) != iProver_top ),
% 2.76/1.03      inference(demodulation,[status(thm)],[c_2386,c_1300]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_24,negated_conjecture,
% 2.76/1.03      ( r2_hidden(k4_tarski(sK9,sK8),sK7)
% 2.76/1.03      | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) ),
% 2.76/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1299,plain,
% 2.76/1.03      ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.76/1.03      | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) = iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1552,plain,
% 2.76/1.03      ( m1_subset_1(X0,sK6) != iProver_top
% 2.76/1.03      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
% 2.76/1.03      | r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_1299,c_1300]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_13,plain,
% 2.76/1.03      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 2.76/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1644,plain,
% 2.76/1.03      ( ~ r2_hidden(k4_tarski(sK9,sK8),sK7)
% 2.76/1.03      | r2_hidden(sK8,k2_relat_1(sK7)) ),
% 2.76/1.03      inference(instantiation,[status(thm)],[c_13]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1645,plain,
% 2.76/1.03      ( r2_hidden(k4_tarski(sK9,sK8),sK7) != iProver_top
% 2.76/1.03      | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_1644]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2448,plain,
% 2.76/1.03      ( r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
% 2.76/1.03      | m1_subset_1(X0,sK6) != iProver_top ),
% 2.76/1.03      inference(global_propositional_subsumption,
% 2.76/1.03                [status(thm)],
% 2.76/1.03                [c_2392,c_1552,c_1645]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2449,plain,
% 2.76/1.03      ( m1_subset_1(X0,sK6) != iProver_top
% 2.76/1.03      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top ),
% 2.76/1.03      inference(renaming,[status(thm)],[c_2448]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2957,plain,
% 2.76/1.03      ( m1_subset_1(sK4(sK8,X0,sK7),sK6) != iProver_top
% 2.76/1.03      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.76/1.03      | v1_relat_1(sK7) != iProver_top ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_1304,c_2449]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_3625,plain,
% 2.76/1.03      ( r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.76/1.03      | m1_subset_1(sK4(sK8,X0,sK7),sK6) != iProver_top ),
% 2.76/1.03      inference(global_propositional_subsumption,
% 2.76/1.03                [status(thm)],
% 2.76/1.03                [c_2957,c_27,c_1693,c_1761]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_3626,plain,
% 2.76/1.03      ( m1_subset_1(sK4(sK8,X0,sK7),sK6) != iProver_top
% 2.76/1.03      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
% 2.76/1.03      inference(renaming,[status(thm)],[c_3625]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_4834,plain,
% 2.76/1.03      ( r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_3853,c_3626]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_4840,plain,
% 2.76/1.03      ( r2_hidden(sK8,k2_relat_1(sK7)) != iProver_top ),
% 2.76/1.03      inference(superposition,[status(thm)],[c_2814,c_4834]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_25,negated_conjecture,
% 2.76/1.03      ( m1_subset_1(sK9,sK6) | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) ),
% 2.76/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_1298,plain,
% 2.76/1.03      ( m1_subset_1(sK9,sK6) = iProver_top
% 2.76/1.03      | r2_hidden(sK8,k2_relset_1(sK6,sK5,sK7)) = iProver_top ),
% 2.76/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2391,plain,
% 2.76/1.03      ( m1_subset_1(sK9,sK6) = iProver_top
% 2.76/1.03      | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
% 2.76/1.03      inference(demodulation,[status(thm)],[c_2386,c_1298]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2390,plain,
% 2.76/1.03      ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.76/1.03      | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
% 2.76/1.03      inference(demodulation,[status(thm)],[c_2386,c_1299]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(c_2816,plain,
% 2.76/1.03      ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
% 2.76/1.03      inference(global_propositional_subsumption,
% 2.76/1.03                [status(thm)],
% 2.76/1.03                [c_2391,c_1645,c_2390]) ).
% 2.76/1.03  
% 2.76/1.03  cnf(contradiction,plain,
% 2.76/1.03      ( $false ),
% 2.76/1.03      inference(minisat,[status(thm)],[c_4840,c_2816]) ).
% 2.76/1.03  
% 2.76/1.03  
% 2.76/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/1.03  
% 2.76/1.03  ------                               Statistics
% 2.76/1.03  
% 2.76/1.03  ------ General
% 2.76/1.03  
% 2.76/1.03  abstr_ref_over_cycles:                  0
% 2.76/1.03  abstr_ref_under_cycles:                 0
% 2.76/1.03  gc_basic_clause_elim:                   0
% 2.76/1.03  forced_gc_time:                         0
% 2.76/1.03  parsing_time:                           0.013
% 2.76/1.03  unif_index_cands_time:                  0.
% 2.76/1.03  unif_index_add_time:                    0.
% 2.76/1.03  orderings_time:                         0.
% 2.76/1.03  out_proof_time:                         0.008
% 2.76/1.03  total_time:                             0.198
% 2.76/1.03  num_of_symbols:                         54
% 2.76/1.03  num_of_terms:                           6542
% 2.76/1.03  
% 2.76/1.03  ------ Preprocessing
% 2.76/1.03  
% 2.76/1.03  num_of_splits:                          0
% 2.76/1.03  num_of_split_atoms:                     0
% 2.76/1.03  num_of_reused_defs:                     0
% 2.76/1.03  num_eq_ax_congr_red:                    52
% 2.76/1.03  num_of_sem_filtered_clauses:            1
% 2.76/1.03  num_of_subtypes:                        0
% 2.76/1.03  monotx_restored_types:                  0
% 2.76/1.03  sat_num_of_epr_types:                   0
% 2.76/1.03  sat_num_of_non_cyclic_types:            0
% 2.76/1.03  sat_guarded_non_collapsed_types:        0
% 2.76/1.03  num_pure_diseq_elim:                    0
% 2.76/1.03  simp_replaced_by:                       0
% 2.76/1.03  res_preprocessed:                       122
% 2.76/1.03  prep_upred:                             0
% 2.76/1.03  prep_unflattend:                        34
% 2.76/1.03  smt_new_axioms:                         0
% 2.76/1.03  pred_elim_cands:                        3
% 2.76/1.03  pred_elim:                              2
% 2.76/1.03  pred_elim_cl:                           3
% 2.76/1.03  pred_elim_cycles:                       4
% 2.76/1.03  merged_defs:                            0
% 2.76/1.03  merged_defs_ncl:                        0
% 2.76/1.03  bin_hyper_res:                          0
% 2.76/1.03  prep_cycles:                            4
% 2.76/1.03  pred_elim_time:                         0.011
% 2.76/1.03  splitting_time:                         0.
% 2.76/1.03  sem_filter_time:                        0.
% 2.76/1.03  monotx_time:                            0.001
% 2.76/1.03  subtype_inf_time:                       0.
% 2.76/1.03  
% 2.76/1.03  ------ Problem properties
% 2.76/1.03  
% 2.76/1.03  clauses:                                24
% 2.76/1.03  conjectures:                            4
% 2.76/1.03  epr:                                    1
% 2.76/1.03  horn:                                   19
% 2.76/1.03  ground:                                 3
% 2.76/1.03  unary:                                  2
% 2.76/1.03  binary:                                 9
% 2.76/1.03  lits:                                   62
% 2.76/1.03  lits_eq:                                8
% 2.76/1.03  fd_pure:                                0
% 2.76/1.03  fd_pseudo:                              0
% 2.76/1.03  fd_cond:                                0
% 2.76/1.03  fd_pseudo_cond:                         5
% 2.76/1.03  ac_symbols:                             0
% 2.76/1.03  
% 2.76/1.03  ------ Propositional Solver
% 2.76/1.03  
% 2.76/1.03  prop_solver_calls:                      26
% 2.76/1.03  prop_fast_solver_calls:                 842
% 2.76/1.03  smt_solver_calls:                       0
% 2.76/1.03  smt_fast_solver_calls:                  0
% 2.76/1.03  prop_num_of_clauses:                    1936
% 2.76/1.03  prop_preprocess_simplified:             5503
% 2.76/1.03  prop_fo_subsumed:                       9
% 2.76/1.03  prop_solver_time:                       0.
% 2.76/1.03  smt_solver_time:                        0.
% 2.76/1.03  smt_fast_solver_time:                   0.
% 2.76/1.03  prop_fast_solver_time:                  0.
% 2.76/1.03  prop_unsat_core_time:                   0.
% 2.76/1.03  
% 2.76/1.03  ------ QBF
% 2.76/1.03  
% 2.76/1.03  qbf_q_res:                              0
% 2.76/1.03  qbf_num_tautologies:                    0
% 2.76/1.03  qbf_prep_cycles:                        0
% 2.76/1.03  
% 2.76/1.03  ------ BMC1
% 2.76/1.03  
% 2.76/1.03  bmc1_current_bound:                     -1
% 2.76/1.03  bmc1_last_solved_bound:                 -1
% 2.76/1.03  bmc1_unsat_core_size:                   -1
% 2.76/1.03  bmc1_unsat_core_parents_size:           -1
% 2.76/1.03  bmc1_merge_next_fun:                    0
% 2.76/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.76/1.03  
% 2.76/1.03  ------ Instantiation
% 2.76/1.03  
% 2.76/1.03  inst_num_of_clauses:                    445
% 2.76/1.03  inst_num_in_passive:                    134
% 2.76/1.03  inst_num_in_active:                     194
% 2.76/1.03  inst_num_in_unprocessed:                117
% 2.76/1.03  inst_num_of_loops:                      250
% 2.76/1.03  inst_num_of_learning_restarts:          0
% 2.76/1.03  inst_num_moves_active_passive:          53
% 2.76/1.03  inst_lit_activity:                      0
% 2.76/1.03  inst_lit_activity_moves:                0
% 2.76/1.03  inst_num_tautologies:                   0
% 2.76/1.03  inst_num_prop_implied:                  0
% 2.76/1.03  inst_num_existing_simplified:           0
% 2.76/1.03  inst_num_eq_res_simplified:             0
% 2.76/1.03  inst_num_child_elim:                    0
% 2.76/1.03  inst_num_of_dismatching_blockings:      54
% 2.76/1.03  inst_num_of_non_proper_insts:           230
% 2.76/1.03  inst_num_of_duplicates:                 0
% 2.76/1.03  inst_inst_num_from_inst_to_res:         0
% 2.76/1.03  inst_dismatching_checking_time:         0.
% 2.76/1.03  
% 2.76/1.03  ------ Resolution
% 2.76/1.03  
% 2.76/1.03  res_num_of_clauses:                     0
% 2.76/1.03  res_num_in_passive:                     0
% 2.76/1.03  res_num_in_active:                      0
% 2.76/1.03  res_num_of_loops:                       126
% 2.76/1.03  res_forward_subset_subsumed:            7
% 2.76/1.03  res_backward_subset_subsumed:           0
% 2.76/1.03  res_forward_subsumed:                   0
% 2.76/1.03  res_backward_subsumed:                  0
% 2.76/1.03  res_forward_subsumption_resolution:     0
% 2.76/1.03  res_backward_subsumption_resolution:    0
% 2.76/1.03  res_clause_to_clause_subsumption:       364
% 2.76/1.03  res_orphan_elimination:                 0
% 2.76/1.03  res_tautology_del:                      16
% 2.76/1.03  res_num_eq_res_simplified:              0
% 2.76/1.03  res_num_sel_changes:                    0
% 2.76/1.03  res_moves_from_active_to_pass:          0
% 2.76/1.03  
% 2.76/1.03  ------ Superposition
% 2.76/1.03  
% 2.76/1.03  sup_time_total:                         0.
% 2.76/1.03  sup_time_generating:                    0.
% 2.76/1.03  sup_time_sim_full:                      0.
% 2.76/1.03  sup_time_sim_immed:                     0.
% 2.76/1.03  
% 2.76/1.03  sup_num_of_clauses:                     119
% 2.76/1.03  sup_num_in_active:                      44
% 2.76/1.03  sup_num_in_passive:                     75
% 2.76/1.03  sup_num_of_loops:                       49
% 2.76/1.03  sup_fw_superposition:                   36
% 2.76/1.03  sup_bw_superposition:                   74
% 2.76/1.03  sup_immediate_simplified:               5
% 2.76/1.03  sup_given_eliminated:                   0
% 2.76/1.03  comparisons_done:                       0
% 2.76/1.03  comparisons_avoided:                    0
% 2.76/1.03  
% 2.76/1.03  ------ Simplifications
% 2.76/1.03  
% 2.76/1.03  
% 2.76/1.03  sim_fw_subset_subsumed:                 0
% 2.76/1.03  sim_bw_subset_subsumed:                 2
% 2.76/1.03  sim_fw_subsumed:                        2
% 2.76/1.03  sim_bw_subsumed:                        2
% 2.76/1.03  sim_fw_subsumption_res:                 1
% 2.76/1.03  sim_bw_subsumption_res:                 0
% 2.76/1.03  sim_tautology_del:                      10
% 2.76/1.03  sim_eq_tautology_del:                   0
% 2.76/1.03  sim_eq_res_simp:                        4
% 2.76/1.03  sim_fw_demodulated:                     0
% 2.76/1.03  sim_bw_demodulated:                     5
% 2.76/1.03  sim_light_normalised:                   0
% 2.76/1.03  sim_joinable_taut:                      0
% 2.76/1.03  sim_joinable_simp:                      0
% 2.76/1.03  sim_ac_normalised:                      0
% 2.76/1.03  sim_smt_subsumption:                    0
% 2.76/1.03  
%------------------------------------------------------------------------------

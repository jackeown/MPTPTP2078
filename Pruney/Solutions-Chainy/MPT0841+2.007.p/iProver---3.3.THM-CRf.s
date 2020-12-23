%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:59 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  125 (1163 expanded)
%              Number of clauses        :   64 ( 380 expanded)
%              Number of leaves         :   18 ( 258 expanded)
%              Depth                    :   25
%              Number of atoms          :  527 (6774 expanded)
%              Number of equality atoms :  138 ( 515 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X5,X4),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X6,X4),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK11,X1)
        & r2_hidden(k4_tarski(sK11,X4),X3)
        & m1_subset_1(sK11,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X6,X4),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(X5,X1)
              | ~ r2_hidden(k4_tarski(X5,sK10),X3)
              | ~ m1_subset_1(X5,X2) )
          | ~ r2_hidden(sK10,k7_relset_1(X2,X0,X3,X1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,X1)
              & r2_hidden(k4_tarski(X6,sK10),X3)
              & m1_subset_1(X6,X2) )
          | r2_hidden(sK10,k7_relset_1(X2,X0,X3,X1)) )
        & m1_subset_1(sK10,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X5,X4),X3)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X6,X4),X3)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK7)
                | ~ r2_hidden(k4_tarski(X5,X4),sK9)
                | ~ m1_subset_1(X5,sK8) )
            | ~ r2_hidden(X4,k7_relset_1(sK8,sK6,sK9,sK7)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK7)
                & r2_hidden(k4_tarski(X6,X4),sK9)
                & m1_subset_1(X6,sK8) )
            | r2_hidden(X4,k7_relset_1(sK8,sK6,sK9,sK7)) )
          & m1_subset_1(X4,sK6) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK7)
          | ~ r2_hidden(k4_tarski(X5,sK10),sK9)
          | ~ m1_subset_1(X5,sK8) )
      | ~ r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) )
    & ( ( r2_hidden(sK11,sK7)
        & r2_hidden(k4_tarski(sK11,sK10),sK9)
        & m1_subset_1(sK11,sK8) )
      | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) )
    & m1_subset_1(sK10,sK6)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f40,f43,f42,f41])).

fof(f65,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,
    ( r2_hidden(sK11,sK7)
    | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
            & r2_hidden(sK0(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK0(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                    & r2_hidden(sK0(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f47,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK7)
      | ~ r2_hidden(k4_tarski(X5,sK10),sK9)
      | ~ m1_subset_1(X5,sK8)
      | ~ r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK9)
    | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f54])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1412,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1418,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2443,plain,
    ( k7_relset_1(sK8,sK6,sK9,X0) = k9_relat_1(sK9,X0) ),
    inference(superposition,[status(thm)],[c_1412,c_1418])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK11,sK7)
    | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1416,plain,
    ( r2_hidden(sK11,sK7) = iProver_top
    | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2716,plain,
    ( r2_hidden(sK11,sK7) = iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2443,c_1416])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1420,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1434,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2315,plain,
    ( v1_relat_1(k2_zfmisc_1(sK8,sK6)) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1434])).

cnf(c_26,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1646,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1903,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_relat_1(k2_zfmisc_1(sK8,sK6))
    | v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1646])).

cnf(c_1904,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK8,sK6)) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2055,plain,
    ( v1_relat_1(k2_zfmisc_1(sK8,sK6)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2056,plain,
    ( v1_relat_1(k2_zfmisc_1(sK8,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2055])).

cnf(c_2434,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2315,c_26,c_1904,c_2056])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_18,c_17])).

cnf(c_1411,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_1898,plain,
    ( k7_relat_1(sK9,sK8) = sK9
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1411])).

cnf(c_2439,plain,
    ( k7_relat_1(sK9,sK8) = sK9 ),
    inference(superposition,[status(thm)],[c_2434,c_1898])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1428,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1)) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k7_relat_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3042,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top
    | v1_relat_1(k7_relat_1(sK9,sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2439,c_1428])).

cnf(c_3047,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3042,c_2439])).

cnf(c_3868,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top
    | r2_hidden(X0,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3047,c_26,c_1904,c_2056])).

cnf(c_3869,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_3868])).

cnf(c_3879,plain,
    ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK9),sK8) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_3869])).

cnf(c_4492,plain,
    ( r2_hidden(sK5(X0,X1,sK9),sK8) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3879,c_26,c_1904,c_2056])).

cnf(c_4493,plain,
    ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,sK9),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_4492])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1435,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4500,plain,
    ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | m1_subset_1(sK5(X0,X1,sK9),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_4493,c_1435])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK5(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1421,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(k4_tarski(X0,sK10),sK9)
    | ~ r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7))
    | ~ m1_subset_1(X0,sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1417,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK9) != iProver_top
    | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) != iProver_top
    | m1_subset_1(X0,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2718,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,sK10),sK9) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
    | m1_subset_1(X0,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2443,c_1417])).

cnf(c_2969,plain,
    ( r2_hidden(sK5(sK10,X0,sK9),sK7) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,X0)) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
    | m1_subset_1(sK5(sK10,X0,sK9),sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_2718])).

cnf(c_3596,plain,
    ( m1_subset_1(sK5(sK10,X0,sK9),sK8) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,X0)) != iProver_top
    | r2_hidden(sK5(sK10,X0,sK9),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2969,c_26,c_1904,c_2056])).

cnf(c_3597,plain,
    ( r2_hidden(sK5(sK10,X0,sK9),sK7) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,X0)) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
    | m1_subset_1(sK5(sK10,X0,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_3596])).

cnf(c_3606,plain,
    ( r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
    | m1_subset_1(sK5(sK10,sK7,sK9),sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_3597])).

cnf(c_4403,plain,
    ( m1_subset_1(sK5(sK10,sK7,sK9),sK8) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3606,c_26,c_1904,c_2056])).

cnf(c_4404,plain,
    ( r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
    | m1_subset_1(sK5(sK10,sK7,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_4403])).

cnf(c_4945,plain,
    ( r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4500,c_4404])).

cnf(c_5341,plain,
    ( r2_hidden(sK11,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2716,c_4945])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(k4_tarski(sK11,sK10),sK9)
    | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1415,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK9) = iProver_top
    | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2715,plain,
    ( r2_hidden(k4_tarski(sK11,sK10),sK9) = iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2443,c_1415])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1422,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1425,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1541,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1422,c_1425])).

cnf(c_4653,plain,
    ( r2_hidden(sK11,X0) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,sK7)) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_1541])).

cnf(c_5181,plain,
    ( r2_hidden(sK11,X0) != iProver_top
    | r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4653,c_26,c_1904,c_2056,c_4945])).

cnf(c_5342,plain,
    ( r2_hidden(sK11,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5181,c_4945])).

cnf(c_5346,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5341,c_5342])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:07 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.70/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/0.99  
% 2.70/0.99  ------  iProver source info
% 2.70/0.99  
% 2.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/0.99  git: non_committed_changes: false
% 2.70/0.99  git: last_make_outside_of_git: false
% 2.70/0.99  
% 2.70/0.99  ------ 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options
% 2.70/0.99  
% 2.70/0.99  --out_options                           all
% 2.70/0.99  --tptp_safe_out                         true
% 2.70/0.99  --problem_path                          ""
% 2.70/0.99  --include_path                          ""
% 2.70/0.99  --clausifier                            res/vclausify_rel
% 2.70/0.99  --clausifier_options                    --mode clausify
% 2.70/0.99  --stdin                                 false
% 2.70/0.99  --stats_out                             all
% 2.70/0.99  
% 2.70/0.99  ------ General Options
% 2.70/0.99  
% 2.70/0.99  --fof                                   false
% 2.70/0.99  --time_out_real                         305.
% 2.70/0.99  --time_out_virtual                      -1.
% 2.70/0.99  --symbol_type_check                     false
% 2.70/0.99  --clausify_out                          false
% 2.70/0.99  --sig_cnt_out                           false
% 2.70/0.99  --trig_cnt_out                          false
% 2.70/0.99  --trig_cnt_out_tolerance                1.
% 2.70/0.99  --trig_cnt_out_sk_spl                   false
% 2.70/0.99  --abstr_cl_out                          false
% 2.70/0.99  
% 2.70/0.99  ------ Global Options
% 2.70/0.99  
% 2.70/0.99  --schedule                              default
% 2.70/0.99  --add_important_lit                     false
% 2.70/0.99  --prop_solver_per_cl                    1000
% 2.70/0.99  --min_unsat_core                        false
% 2.70/0.99  --soft_assumptions                      false
% 2.70/0.99  --soft_lemma_size                       3
% 2.70/0.99  --prop_impl_unit_size                   0
% 2.70/0.99  --prop_impl_unit                        []
% 2.70/0.99  --share_sel_clauses                     true
% 2.70/0.99  --reset_solvers                         false
% 2.70/0.99  --bc_imp_inh                            [conj_cone]
% 2.70/0.99  --conj_cone_tolerance                   3.
% 2.70/0.99  --extra_neg_conj                        none
% 2.70/0.99  --large_theory_mode                     true
% 2.70/0.99  --prolific_symb_bound                   200
% 2.70/0.99  --lt_threshold                          2000
% 2.70/0.99  --clause_weak_htbl                      true
% 2.70/0.99  --gc_record_bc_elim                     false
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing Options
% 2.70/0.99  
% 2.70/0.99  --preprocessing_flag                    true
% 2.70/0.99  --time_out_prep_mult                    0.1
% 2.70/0.99  --splitting_mode                        input
% 2.70/0.99  --splitting_grd                         true
% 2.70/0.99  --splitting_cvd                         false
% 2.70/0.99  --splitting_cvd_svl                     false
% 2.70/0.99  --splitting_nvd                         32
% 2.70/0.99  --sub_typing                            true
% 2.70/0.99  --prep_gs_sim                           true
% 2.70/0.99  --prep_unflatten                        true
% 2.70/0.99  --prep_res_sim                          true
% 2.70/0.99  --prep_upred                            true
% 2.70/0.99  --prep_sem_filter                       exhaustive
% 2.70/0.99  --prep_sem_filter_out                   false
% 2.70/0.99  --pred_elim                             true
% 2.70/0.99  --res_sim_input                         true
% 2.70/0.99  --eq_ax_congr_red                       true
% 2.70/0.99  --pure_diseq_elim                       true
% 2.70/0.99  --brand_transform                       false
% 2.70/0.99  --non_eq_to_eq                          false
% 2.70/0.99  --prep_def_merge                        true
% 2.70/0.99  --prep_def_merge_prop_impl              false
% 2.70/0.99  --prep_def_merge_mbd                    true
% 2.70/0.99  --prep_def_merge_tr_red                 false
% 2.70/0.99  --prep_def_merge_tr_cl                  false
% 2.70/0.99  --smt_preprocessing                     true
% 2.70/0.99  --smt_ac_axioms                         fast
% 2.70/0.99  --preprocessed_out                      false
% 2.70/0.99  --preprocessed_stats                    false
% 2.70/0.99  
% 2.70/0.99  ------ Abstraction refinement Options
% 2.70/0.99  
% 2.70/0.99  --abstr_ref                             []
% 2.70/0.99  --abstr_ref_prep                        false
% 2.70/0.99  --abstr_ref_until_sat                   false
% 2.70/0.99  --abstr_ref_sig_restrict                funpre
% 2.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.99  --abstr_ref_under                       []
% 2.70/0.99  
% 2.70/0.99  ------ SAT Options
% 2.70/0.99  
% 2.70/0.99  --sat_mode                              false
% 2.70/0.99  --sat_fm_restart_options                ""
% 2.70/0.99  --sat_gr_def                            false
% 2.70/0.99  --sat_epr_types                         true
% 2.70/0.99  --sat_non_cyclic_types                  false
% 2.70/0.99  --sat_finite_models                     false
% 2.70/0.99  --sat_fm_lemmas                         false
% 2.70/0.99  --sat_fm_prep                           false
% 2.70/0.99  --sat_fm_uc_incr                        true
% 2.70/0.99  --sat_out_model                         small
% 2.70/0.99  --sat_out_clauses                       false
% 2.70/0.99  
% 2.70/0.99  ------ QBF Options
% 2.70/0.99  
% 2.70/0.99  --qbf_mode                              false
% 2.70/0.99  --qbf_elim_univ                         false
% 2.70/0.99  --qbf_dom_inst                          none
% 2.70/0.99  --qbf_dom_pre_inst                      false
% 2.70/0.99  --qbf_sk_in                             false
% 2.70/0.99  --qbf_pred_elim                         true
% 2.70/0.99  --qbf_split                             512
% 2.70/0.99  
% 2.70/0.99  ------ BMC1 Options
% 2.70/0.99  
% 2.70/0.99  --bmc1_incremental                      false
% 2.70/0.99  --bmc1_axioms                           reachable_all
% 2.70/0.99  --bmc1_min_bound                        0
% 2.70/0.99  --bmc1_max_bound                        -1
% 2.70/0.99  --bmc1_max_bound_default                -1
% 2.70/0.99  --bmc1_symbol_reachability              true
% 2.70/0.99  --bmc1_property_lemmas                  false
% 2.70/0.99  --bmc1_k_induction                      false
% 2.70/0.99  --bmc1_non_equiv_states                 false
% 2.70/0.99  --bmc1_deadlock                         false
% 2.70/0.99  --bmc1_ucm                              false
% 2.70/0.99  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         false
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     num_symb
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       true
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     false
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   []
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_full_bw                           [BwDemod]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  ------ Parsing...
% 2.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/0.99  ------ Proving...
% 2.70/0.99  ------ Problem Properties 
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  clauses                                 25
% 2.70/0.99  conjectures                             6
% 2.70/0.99  EPR                                     2
% 2.70/0.99  Horn                                    19
% 2.70/0.99  unary                                   3
% 2.70/0.99  binary                                  7
% 2.70/0.99  lits                                    76
% 2.70/0.99  lits eq                                 7
% 2.70/0.99  fd_pure                                 0
% 2.70/0.99  fd_pseudo                               0
% 2.70/0.99  fd_cond                                 0
% 2.70/0.99  fd_pseudo_cond                          5
% 2.70/0.99  AC symbols                              0
% 2.70/0.99  
% 2.70/0.99  ------ Schedule dynamic 5 is on 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ 
% 2.70/0.99  Current options:
% 2.70/0.99  ------ 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options
% 2.70/0.99  
% 2.70/0.99  --out_options                           all
% 2.70/0.99  --tptp_safe_out                         true
% 2.70/0.99  --problem_path                          ""
% 2.70/0.99  --include_path                          ""
% 2.70/0.99  --clausifier                            res/vclausify_rel
% 2.70/0.99  --clausifier_options                    --mode clausify
% 2.70/0.99  --stdin                                 false
% 2.70/0.99  --stats_out                             all
% 2.70/0.99  
% 2.70/0.99  ------ General Options
% 2.70/0.99  
% 2.70/0.99  --fof                                   false
% 2.70/0.99  --time_out_real                         305.
% 2.70/0.99  --time_out_virtual                      -1.
% 2.70/0.99  --symbol_type_check                     false
% 2.70/0.99  --clausify_out                          false
% 2.70/0.99  --sig_cnt_out                           false
% 2.70/0.99  --trig_cnt_out                          false
% 2.70/0.99  --trig_cnt_out_tolerance                1.
% 2.70/0.99  --trig_cnt_out_sk_spl                   false
% 2.70/0.99  --abstr_cl_out                          false
% 2.70/0.99  
% 2.70/0.99  ------ Global Options
% 2.70/0.99  
% 2.70/0.99  --schedule                              default
% 2.70/0.99  --add_important_lit                     false
% 2.70/0.99  --prop_solver_per_cl                    1000
% 2.70/0.99  --min_unsat_core                        false
% 2.70/0.99  --soft_assumptions                      false
% 2.70/0.99  --soft_lemma_size                       3
% 2.70/0.99  --prop_impl_unit_size                   0
% 2.70/0.99  --prop_impl_unit                        []
% 2.70/0.99  --share_sel_clauses                     true
% 2.70/0.99  --reset_solvers                         false
% 2.70/0.99  --bc_imp_inh                            [conj_cone]
% 2.70/0.99  --conj_cone_tolerance                   3.
% 2.70/0.99  --extra_neg_conj                        none
% 2.70/0.99  --large_theory_mode                     true
% 2.70/0.99  --prolific_symb_bound                   200
% 2.70/0.99  --lt_threshold                          2000
% 2.70/0.99  --clause_weak_htbl                      true
% 2.70/0.99  --gc_record_bc_elim                     false
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing Options
% 2.70/0.99  
% 2.70/0.99  --preprocessing_flag                    true
% 2.70/0.99  --time_out_prep_mult                    0.1
% 2.70/0.99  --splitting_mode                        input
% 2.70/0.99  --splitting_grd                         true
% 2.70/0.99  --splitting_cvd                         false
% 2.70/0.99  --splitting_cvd_svl                     false
% 2.70/0.99  --splitting_nvd                         32
% 2.70/0.99  --sub_typing                            true
% 2.70/0.99  --prep_gs_sim                           true
% 2.70/0.99  --prep_unflatten                        true
% 2.70/0.99  --prep_res_sim                          true
% 2.70/0.99  --prep_upred                            true
% 2.70/0.99  --prep_sem_filter                       exhaustive
% 2.70/0.99  --prep_sem_filter_out                   false
% 2.70/0.99  --pred_elim                             true
% 2.70/0.99  --res_sim_input                         true
% 2.70/0.99  --eq_ax_congr_red                       true
% 2.70/0.99  --pure_diseq_elim                       true
% 2.70/0.99  --brand_transform                       false
% 2.70/0.99  --non_eq_to_eq                          false
% 2.70/0.99  --prep_def_merge                        true
% 2.70/0.99  --prep_def_merge_prop_impl              false
% 2.70/0.99  --prep_def_merge_mbd                    true
% 2.70/0.99  --prep_def_merge_tr_red                 false
% 2.70/0.99  --prep_def_merge_tr_cl                  false
% 2.70/0.99  --smt_preprocessing                     true
% 2.70/0.99  --smt_ac_axioms                         fast
% 2.70/0.99  --preprocessed_out                      false
% 2.70/0.99  --preprocessed_stats                    false
% 2.70/0.99  
% 2.70/0.99  ------ Abstraction refinement Options
% 2.70/0.99  
% 2.70/0.99  --abstr_ref                             []
% 2.70/0.99  --abstr_ref_prep                        false
% 2.70/0.99  --abstr_ref_until_sat                   false
% 2.70/0.99  --abstr_ref_sig_restrict                funpre
% 2.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.99  --abstr_ref_under                       []
% 2.70/0.99  
% 2.70/0.99  ------ SAT Options
% 2.70/0.99  
% 2.70/0.99  --sat_mode                              false
% 2.70/0.99  --sat_fm_restart_options                ""
% 2.70/0.99  --sat_gr_def                            false
% 2.70/0.99  --sat_epr_types                         true
% 2.70/0.99  --sat_non_cyclic_types                  false
% 2.70/0.99  --sat_finite_models                     false
% 2.70/0.99  --sat_fm_lemmas                         false
% 2.70/0.99  --sat_fm_prep                           false
% 2.70/0.99  --sat_fm_uc_incr                        true
% 2.70/0.99  --sat_out_model                         small
% 2.70/0.99  --sat_out_clauses                       false
% 2.70/0.99  
% 2.70/0.99  ------ QBF Options
% 2.70/0.99  
% 2.70/0.99  --qbf_mode                              false
% 2.70/0.99  --qbf_elim_univ                         false
% 2.70/0.99  --qbf_dom_inst                          none
% 2.70/0.99  --qbf_dom_pre_inst                      false
% 2.70/0.99  --qbf_sk_in                             false
% 2.70/0.99  --qbf_pred_elim                         true
% 2.70/0.99  --qbf_split                             512
% 2.70/0.99  
% 2.70/0.99  ------ BMC1 Options
% 2.70/0.99  
% 2.70/0.99  --bmc1_incremental                      false
% 2.70/0.99  --bmc1_axioms                           reachable_all
% 2.70/0.99  --bmc1_min_bound                        0
% 2.70/0.99  --bmc1_max_bound                        -1
% 2.70/0.99  --bmc1_max_bound_default                -1
% 2.70/0.99  --bmc1_symbol_reachability              true
% 2.70/0.99  --bmc1_property_lemmas                  false
% 2.70/0.99  --bmc1_k_induction                      false
% 2.70/0.99  --bmc1_non_equiv_states                 false
% 2.70/0.99  --bmc1_deadlock                         false
% 2.70/0.99  --bmc1_ucm                              false
% 2.70/0.99  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         false
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     none
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       false
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     false
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   []
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_full_bw                           [BwDemod]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ Proving...
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS status Theorem for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99   Resolution empty clause
% 2.70/0.99  
% 2.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  fof(f10,conjecture,(
% 2.70/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f11,negated_conjecture,(
% 2.70/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.70/0.99    inference(negated_conjecture,[],[f10])).
% 2.70/0.99  
% 2.70/0.99  fof(f12,plain,(
% 2.70/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)))))),
% 2.70/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.70/0.99  
% 2.70/0.99  fof(f22,plain,(
% 2.70/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.70/0.99    inference(ennf_transformation,[],[f12])).
% 2.70/0.99  
% 2.70/0.99  fof(f38,plain,(
% 2.70/0.99    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.70/0.99    inference(nnf_transformation,[],[f22])).
% 2.70/0.99  
% 2.70/0.99  fof(f39,plain,(
% 2.70/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.70/0.99    inference(flattening,[],[f38])).
% 2.70/0.99  
% 2.70/0.99  fof(f40,plain,(
% 2.70/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.70/0.99    inference(rectify,[],[f39])).
% 2.70/0.99  
% 2.70/0.99  fof(f43,plain,(
% 2.70/0.99    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK11,X1) & r2_hidden(k4_tarski(sK11,X4),X3) & m1_subset_1(sK11,X2))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f42,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,sK10),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK10,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,sK10),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK10,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(sK10,X0))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f41,plain,(
% 2.70/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK7) | ~r2_hidden(k4_tarski(X5,X4),sK9) | ~m1_subset_1(X5,sK8)) | ~r2_hidden(X4,k7_relset_1(sK8,sK6,sK9,sK7))) & (? [X6] : (r2_hidden(X6,sK7) & r2_hidden(k4_tarski(X6,X4),sK9) & m1_subset_1(X6,sK8)) | r2_hidden(X4,k7_relset_1(sK8,sK6,sK9,sK7))) & m1_subset_1(X4,sK6)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f44,plain,(
% 2.70/0.99    ((! [X5] : (~r2_hidden(X5,sK7) | ~r2_hidden(k4_tarski(X5,sK10),sK9) | ~m1_subset_1(X5,sK8)) | ~r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7))) & ((r2_hidden(sK11,sK7) & r2_hidden(k4_tarski(sK11,sK10),sK9) & m1_subset_1(sK11,sK8)) | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7))) & m1_subset_1(sK10,sK6)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f40,f43,f42,f41])).
% 2.70/0.99  
% 2.70/0.99  fof(f65,plain,(
% 2.70/0.99    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 2.70/0.99    inference(cnf_transformation,[],[f44])).
% 2.70/0.99  
% 2.70/0.99  fof(f9,axiom,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f21,plain,(
% 2.70/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f9])).
% 2.70/0.99  
% 2.70/0.99  fof(f64,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f21])).
% 2.70/0.99  
% 2.70/0.99  fof(f69,plain,(
% 2.70/0.99    r2_hidden(sK11,sK7) | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7))),
% 2.70/0.99    inference(cnf_transformation,[],[f44])).
% 2.70/0.99  
% 2.70/0.99  fof(f6,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f17,plain,(
% 2.70/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.70/0.99    inference(ennf_transformation,[],[f6])).
% 2.70/0.99  
% 2.70/0.99  fof(f34,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.70/0.99    inference(nnf_transformation,[],[f17])).
% 2.70/0.99  
% 2.70/0.99  fof(f35,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.70/0.99    inference(rectify,[],[f34])).
% 2.70/0.99  
% 2.70/0.99  fof(f36,plain,(
% 2.70/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f37,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 2.70/0.99  
% 2.70/0.99  fof(f59,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f37])).
% 2.70/0.99  
% 2.70/0.99  fof(f2,axiom,(
% 2.70/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f15,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f2])).
% 2.70/0.99  
% 2.70/0.99  fof(f46,plain,(
% 2.70/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f15])).
% 2.70/0.99  
% 2.70/0.99  fof(f5,axiom,(
% 2.70/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f57,plain,(
% 2.70/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f5])).
% 2.70/0.99  
% 2.70/0.99  fof(f8,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f13,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.70/0.99    inference(pure_predicate_removal,[],[f8])).
% 2.70/0.99  
% 2.70/0.99  fof(f20,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f13])).
% 2.70/0.99  
% 2.70/0.99  fof(f63,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f20])).
% 2.70/0.99  
% 2.70/0.99  fof(f7,axiom,(
% 2.70/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f18,plain,(
% 2.70/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.70/0.99    inference(ennf_transformation,[],[f7])).
% 2.70/0.99  
% 2.70/0.99  fof(f19,plain,(
% 2.70/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.70/0.99    inference(flattening,[],[f18])).
% 2.70/0.99  
% 2.70/0.99  fof(f62,plain,(
% 2.70/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f19])).
% 2.70/0.99  
% 2.70/0.99  fof(f3,axiom,(
% 2.70/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f16,plain,(
% 2.70/0.99    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f3])).
% 2.70/0.99  
% 2.70/0.99  fof(f23,plain,(
% 2.70/0.99    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.70/0.99    inference(nnf_transformation,[],[f16])).
% 2.70/0.99  
% 2.70/0.99  fof(f24,plain,(
% 2.70/0.99    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.70/0.99    inference(flattening,[],[f23])).
% 2.70/0.99  
% 2.70/0.99  fof(f25,plain,(
% 2.70/0.99    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.70/0.99    inference(rectify,[],[f24])).
% 2.70/0.99  
% 2.70/0.99  fof(f26,plain,(
% 2.70/0.99    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) & r2_hidden(sK0(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f27,plain,(
% 2.70/0.99    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) & r2_hidden(sK0(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 2.70/0.99  
% 2.70/0.99  fof(f47,plain,(
% 2.70/0.99    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f27])).
% 2.70/0.99  
% 2.70/0.99  fof(f73,plain,(
% 2.70/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.70/0.99    inference(equality_resolution,[],[f47])).
% 2.70/0.99  
% 2.70/0.99  fof(f1,axiom,(
% 2.70/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f14,plain,(
% 2.70/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.70/0.99    inference(ennf_transformation,[],[f1])).
% 2.70/0.99  
% 2.70/0.99  fof(f45,plain,(
% 2.70/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f14])).
% 2.70/0.99  
% 2.70/0.99  fof(f60,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f37])).
% 2.70/0.99  
% 2.70/0.99  fof(f70,plain,(
% 2.70/0.99    ( ! [X5] : (~r2_hidden(X5,sK7) | ~r2_hidden(k4_tarski(X5,sK10),sK9) | ~m1_subset_1(X5,sK8) | ~r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f44])).
% 2.70/0.99  
% 2.70/0.99  fof(f68,plain,(
% 2.70/0.99    r2_hidden(k4_tarski(sK11,sK10),sK9) | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7))),
% 2.70/0.99    inference(cnf_transformation,[],[f44])).
% 2.70/0.99  
% 2.70/0.99  fof(f61,plain,(
% 2.70/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f37])).
% 2.70/0.99  
% 2.70/0.99  fof(f4,axiom,(
% 2.70/0.99    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f28,plain,(
% 2.70/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.70/0.99    inference(nnf_transformation,[],[f4])).
% 2.70/0.99  
% 2.70/0.99  fof(f29,plain,(
% 2.70/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.70/0.99    inference(rectify,[],[f28])).
% 2.70/0.99  
% 2.70/0.99  fof(f32,plain,(
% 2.70/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f31,plain,(
% 2.70/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f30,plain,(
% 2.70/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f33,plain,(
% 2.70/0.99    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).
% 2.70/0.99  
% 2.70/0.99  fof(f54,plain,(
% 2.70/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.70/0.99    inference(cnf_transformation,[],[f33])).
% 2.70/0.99  
% 2.70/0.99  fof(f74,plain,(
% 2.70/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.70/0.99    inference(equality_resolution,[],[f54])).
% 2.70/0.99  
% 2.70/0.99  cnf(c_25,negated_conjecture,
% 2.70/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1412,plain,
% 2.70/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_19,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1418,plain,
% 2.70/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2443,plain,
% 2.70/0.99      ( k7_relset_1(sK8,sK6,sK9,X0) = k9_relat_1(sK9,X0) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1412,c_1418]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_21,negated_conjecture,
% 2.70/0.99      ( r2_hidden(sK11,sK7) | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1416,plain,
% 2.70/0.99      ( r2_hidden(sK11,sK7) = iProver_top
% 2.70/0.99      | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2716,plain,
% 2.70/0.99      ( r2_hidden(sK11,sK7) = iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,sK7)) = iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_2443,c_1416]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_15,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.70/0.99      | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1)
% 2.70/0.99      | ~ v1_relat_1(X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1420,plain,
% 2.70/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1) = iProver_top
% 2.70/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1434,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.70/0.99      | v1_relat_1(X1) != iProver_top
% 2.70/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2315,plain,
% 2.70/0.99      ( v1_relat_1(k2_zfmisc_1(sK8,sK6)) != iProver_top
% 2.70/0.99      | v1_relat_1(sK9) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1412,c_1434]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_26,plain,
% 2.70/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1646,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | v1_relat_1(X0)
% 2.70/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1903,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
% 2.70/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK8,sK6))
% 2.70/0.99      | v1_relat_1(sK9) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1646]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1904,plain,
% 2.70/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
% 2.70/0.99      | v1_relat_1(k2_zfmisc_1(sK8,sK6)) != iProver_top
% 2.70/0.99      | v1_relat_1(sK9) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_12,plain,
% 2.70/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2055,plain,
% 2.70/0.99      ( v1_relat_1(k2_zfmisc_1(sK8,sK6)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2056,plain,
% 2.70/0.99      ( v1_relat_1(k2_zfmisc_1(sK8,sK6)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2055]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2434,plain,
% 2.70/0.99      ( v1_relat_1(sK9) = iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_2315,c_26,c_1904,c_2056]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_18,plain,
% 2.70/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_17,plain,
% 2.70/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_292,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ v1_relat_1(X0)
% 2.70/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.70/0.99      inference(resolution,[status(thm)],[c_18,c_17]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1411,plain,
% 2.70/0.99      ( k7_relat_1(X0,X1) = X0
% 2.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.70/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1898,plain,
% 2.70/0.99      ( k7_relat_1(sK9,sK8) = sK9 | v1_relat_1(sK9) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1412,c_1411]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2439,plain,
% 2.70/0.99      ( k7_relat_1(sK9,sK8) = sK9 ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2434,c_1898]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_7,plain,
% 2.70/0.99      ( r2_hidden(X0,X1)
% 2.70/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
% 2.70/0.99      | ~ v1_relat_1(X3)
% 2.70/0.99      | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1428,plain,
% 2.70/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1)) != iProver_top
% 2.70/0.99      | v1_relat_1(X3) != iProver_top
% 2.70/0.99      | v1_relat_1(k7_relat_1(X3,X1)) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3042,plain,
% 2.70/0.99      ( r2_hidden(X0,sK8) = iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top
% 2.70/0.99      | v1_relat_1(k7_relat_1(sK9,sK8)) != iProver_top
% 2.70/0.99      | v1_relat_1(sK9) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2439,c_1428]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3047,plain,
% 2.70/0.99      ( r2_hidden(X0,sK8) = iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top
% 2.70/0.99      | v1_relat_1(sK9) != iProver_top ),
% 2.70/0.99      inference(light_normalisation,[status(thm)],[c_3042,c_2439]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3868,plain,
% 2.70/0.99      ( r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top
% 2.70/0.99      | r2_hidden(X0,sK8) = iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3047,c_26,c_1904,c_2056]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3869,plain,
% 2.70/0.99      ( r2_hidden(X0,sK8) = iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_3868]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3879,plain,
% 2.70/0.99      ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 2.70/0.99      | r2_hidden(sK5(X0,X1,sK9),sK8) = iProver_top
% 2.70/0.99      | v1_relat_1(sK9) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1420,c_3869]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4492,plain,
% 2.70/0.99      ( r2_hidden(sK5(X0,X1,sK9),sK8) = iProver_top
% 2.70/0.99      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3879,c_26,c_1904,c_2056]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4493,plain,
% 2.70/0.99      ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 2.70/0.99      | r2_hidden(sK5(X0,X1,sK9),sK8) = iProver_top ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_4492]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_0,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1435,plain,
% 2.70/0.99      ( r2_hidden(X0,X1) != iProver_top | m1_subset_1(X0,X1) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4500,plain,
% 2.70/0.99      ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 2.70/0.99      | m1_subset_1(sK5(X0,X1,sK9),sK8) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_4493,c_1435]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_14,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.70/0.99      | r2_hidden(sK5(X0,X2,X1),X2)
% 2.70/0.99      | ~ v1_relat_1(X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1421,plain,
% 2.70/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.70/0.99      | r2_hidden(sK5(X0,X2,X1),X2) = iProver_top
% 2.70/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_20,negated_conjecture,
% 2.70/0.99      ( ~ r2_hidden(X0,sK7)
% 2.70/0.99      | ~ r2_hidden(k4_tarski(X0,sK10),sK9)
% 2.70/0.99      | ~ r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7))
% 2.70/0.99      | ~ m1_subset_1(X0,sK8) ),
% 2.70/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1417,plain,
% 2.70/0.99      ( r2_hidden(X0,sK7) != iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(X0,sK10),sK9) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) != iProver_top
% 2.70/0.99      | m1_subset_1(X0,sK8) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2718,plain,
% 2.70/0.99      ( r2_hidden(X0,sK7) != iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(X0,sK10),sK9) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
% 2.70/0.99      | m1_subset_1(X0,sK8) != iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_2443,c_1417]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2969,plain,
% 2.70/0.99      ( r2_hidden(sK5(sK10,X0,sK9),sK7) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,X0)) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
% 2.70/0.99      | m1_subset_1(sK5(sK10,X0,sK9),sK8) != iProver_top
% 2.70/0.99      | v1_relat_1(sK9) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1420,c_2718]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3596,plain,
% 2.70/0.99      ( m1_subset_1(sK5(sK10,X0,sK9),sK8) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,X0)) != iProver_top
% 2.70/0.99      | r2_hidden(sK5(sK10,X0,sK9),sK7) != iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_2969,c_26,c_1904,c_2056]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3597,plain,
% 2.70/0.99      ( r2_hidden(sK5(sK10,X0,sK9),sK7) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,X0)) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
% 2.70/0.99      | m1_subset_1(sK5(sK10,X0,sK9),sK8) != iProver_top ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_3596]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3606,plain,
% 2.70/0.99      ( r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
% 2.70/0.99      | m1_subset_1(sK5(sK10,sK7,sK9),sK8) != iProver_top
% 2.70/0.99      | v1_relat_1(sK9) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1421,c_3597]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4403,plain,
% 2.70/0.99      ( m1_subset_1(sK5(sK10,sK7,sK9),sK8) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3606,c_26,c_1904,c_2056]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4404,plain,
% 2.70/0.99      ( r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top
% 2.70/0.99      | m1_subset_1(sK5(sK10,sK7,sK9),sK8) != iProver_top ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_4403]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4945,plain,
% 2.70/0.99      ( r2_hidden(sK10,k9_relat_1(sK9,sK7)) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_4500,c_4404]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5341,plain,
% 2.70/0.99      ( r2_hidden(sK11,sK7) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2716,c_4945]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_22,negated_conjecture,
% 2.70/0.99      ( r2_hidden(k4_tarski(sK11,sK10),sK9)
% 2.70/0.99      | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1415,plain,
% 2.70/0.99      ( r2_hidden(k4_tarski(sK11,sK10),sK9) = iProver_top
% 2.70/0.99      | r2_hidden(sK10,k7_relset_1(sK8,sK6,sK9,sK7)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2715,plain,
% 2.70/0.99      ( r2_hidden(k4_tarski(sK11,sK10),sK9) = iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,sK7)) = iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_2443,c_1415]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_13,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,X1)
% 2.70/0.99      | r2_hidden(X2,k9_relat_1(X3,X1))
% 2.70/0.99      | ~ r2_hidden(X0,k1_relat_1(X3))
% 2.70/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 2.70/0.99      | ~ v1_relat_1(X3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1422,plain,
% 2.70/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.70/0.99      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 2.70/0.99      | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 2.70/0.99      | v1_relat_1(X3) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_10,plain,
% 2.70/0.99      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1425,plain,
% 2.70/0.99      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1541,plain,
% 2.70/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.70/0.99      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 2.70/0.99      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 2.70/0.99      | v1_relat_1(X3) != iProver_top ),
% 2.70/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1422,c_1425]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4653,plain,
% 2.70/0.99      ( r2_hidden(sK11,X0) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,sK7)) = iProver_top
% 2.70/0.99      | v1_relat_1(sK9) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2715,c_1541]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5181,plain,
% 2.70/0.99      ( r2_hidden(sK11,X0) != iProver_top
% 2.70/0.99      | r2_hidden(sK10,k9_relat_1(sK9,X0)) = iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_4653,c_26,c_1904,c_2056,c_4945]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5342,plain,
% 2.70/0.99      ( r2_hidden(sK11,sK7) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_5181,c_4945]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5346,plain,
% 2.70/0.99      ( $false ),
% 2.70/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5341,c_5342]) ).
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  ------                               Statistics
% 2.70/0.99  
% 2.70/0.99  ------ General
% 2.70/0.99  
% 2.70/0.99  abstr_ref_over_cycles:                  0
% 2.70/0.99  abstr_ref_under_cycles:                 0
% 2.70/0.99  gc_basic_clause_elim:                   0
% 2.70/0.99  forced_gc_time:                         0
% 2.70/0.99  parsing_time:                           0.009
% 2.70/0.99  unif_index_cands_time:                  0.
% 2.70/0.99  unif_index_add_time:                    0.
% 2.70/0.99  orderings_time:                         0.
% 2.70/0.99  out_proof_time:                         0.009
% 2.70/0.99  total_time:                             0.181
% 2.70/0.99  num_of_symbols:                         54
% 2.70/0.99  num_of_terms:                           6143
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing
% 2.70/0.99  
% 2.70/0.99  num_of_splits:                          0
% 2.70/0.99  num_of_split_atoms:                     0
% 2.70/0.99  num_of_reused_defs:                     0
% 2.70/0.99  num_eq_ax_congr_red:                    62
% 2.70/0.99  num_of_sem_filtered_clauses:            1
% 2.70/0.99  num_of_subtypes:                        0
% 2.70/0.99  monotx_restored_types:                  0
% 2.70/0.99  sat_num_of_epr_types:                   0
% 2.70/0.99  sat_num_of_non_cyclic_types:            0
% 2.70/0.99  sat_guarded_non_collapsed_types:        0
% 2.70/0.99  num_pure_diseq_elim:                    0
% 2.70/0.99  simp_replaced_by:                       0
% 2.70/0.99  res_preprocessed:                       120
% 2.70/0.99  prep_upred:                             0
% 2.70/0.99  prep_unflattend:                        40
% 2.70/0.99  smt_new_axioms:                         0
% 2.70/0.99  pred_elim_cands:                        3
% 2.70/0.99  pred_elim:                              1
% 2.70/0.99  pred_elim_cl:                           1
% 2.70/0.99  pred_elim_cycles:                       3
% 2.70/0.99  merged_defs:                            0
% 2.70/0.99  merged_defs_ncl:                        0
% 2.70/0.99  bin_hyper_res:                          0
% 2.70/0.99  prep_cycles:                            4
% 2.70/0.99  pred_elim_time:                         0.009
% 2.70/0.99  splitting_time:                         0.
% 2.70/0.99  sem_filter_time:                        0.
% 2.70/0.99  monotx_time:                            0.001
% 2.70/0.99  subtype_inf_time:                       0.
% 2.70/0.99  
% 2.70/0.99  ------ Problem properties
% 2.70/0.99  
% 2.70/0.99  clauses:                                25
% 2.70/0.99  conjectures:                            6
% 2.70/0.99  epr:                                    2
% 2.70/0.99  horn:                                   19
% 2.70/0.99  ground:                                 5
% 2.70/0.99  unary:                                  3
% 2.70/0.99  binary:                                 7
% 2.70/0.99  lits:                                   76
% 2.70/0.99  lits_eq:                                7
% 2.70/0.99  fd_pure:                                0
% 2.70/0.99  fd_pseudo:                              0
% 2.70/0.99  fd_cond:                                0
% 2.70/0.99  fd_pseudo_cond:                         5
% 2.70/0.99  ac_symbols:                             0
% 2.70/0.99  
% 2.70/0.99  ------ Propositional Solver
% 2.70/0.99  
% 2.70/0.99  prop_solver_calls:                      28
% 2.70/0.99  prop_fast_solver_calls:                 1038
% 2.70/0.99  smt_solver_calls:                       0
% 2.70/0.99  smt_fast_solver_calls:                  0
% 2.70/0.99  prop_num_of_clauses:                    1922
% 2.70/0.99  prop_preprocess_simplified:             5429
% 2.70/0.99  prop_fo_subsumed:                       14
% 2.70/0.99  prop_solver_time:                       0.
% 2.70/0.99  smt_solver_time:                        0.
% 2.70/0.99  smt_fast_solver_time:                   0.
% 2.70/0.99  prop_fast_solver_time:                  0.
% 2.70/0.99  prop_unsat_core_time:                   0.
% 2.70/0.99  
% 2.70/0.99  ------ QBF
% 2.70/0.99  
% 2.70/0.99  qbf_q_res:                              0
% 2.70/0.99  qbf_num_tautologies:                    0
% 2.70/0.99  qbf_prep_cycles:                        0
% 2.70/0.99  
% 2.70/0.99  ------ BMC1
% 2.70/0.99  
% 2.70/0.99  bmc1_current_bound:                     -1
% 2.70/0.99  bmc1_last_solved_bound:                 -1
% 2.70/0.99  bmc1_unsat_core_size:                   -1
% 2.70/0.99  bmc1_unsat_core_parents_size:           -1
% 2.70/0.99  bmc1_merge_next_fun:                    0
% 2.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation
% 2.70/0.99  
% 2.70/0.99  inst_num_of_clauses:                    440
% 2.70/0.99  inst_num_in_passive:                    30
% 2.70/0.99  inst_num_in_active:                     261
% 2.70/0.99  inst_num_in_unprocessed:                149
% 2.70/0.99  inst_num_of_loops:                      330
% 2.70/0.99  inst_num_of_learning_restarts:          0
% 2.70/0.99  inst_num_moves_active_passive:          66
% 2.70/0.99  inst_lit_activity:                      0
% 2.70/0.99  inst_lit_activity_moves:                0
% 2.70/0.99  inst_num_tautologies:                   0
% 2.70/0.99  inst_num_prop_implied:                  0
% 2.70/0.99  inst_num_existing_simplified:           0
% 2.70/0.99  inst_num_eq_res_simplified:             0
% 2.70/0.99  inst_num_child_elim:                    0
% 2.70/0.99  inst_num_of_dismatching_blockings:      133
% 2.70/0.99  inst_num_of_non_proper_insts:           328
% 2.70/0.99  inst_num_of_duplicates:                 0
% 2.70/0.99  inst_inst_num_from_inst_to_res:         0
% 2.70/0.99  inst_dismatching_checking_time:         0.
% 2.70/0.99  
% 2.70/0.99  ------ Resolution
% 2.70/0.99  
% 2.70/0.99  res_num_of_clauses:                     0
% 2.70/0.99  res_num_in_passive:                     0
% 2.70/0.99  res_num_in_active:                      0
% 2.70/0.99  res_num_of_loops:                       124
% 2.70/0.99  res_forward_subset_subsumed:            19
% 2.70/0.99  res_backward_subset_subsumed:           0
% 2.70/0.99  res_forward_subsumed:                   0
% 2.70/0.99  res_backward_subsumed:                  0
% 2.70/0.99  res_forward_subsumption_resolution:     0
% 2.70/0.99  res_backward_subsumption_resolution:    0
% 2.70/0.99  res_clause_to_clause_subsumption:       302
% 2.70/0.99  res_orphan_elimination:                 0
% 2.70/0.99  res_tautology_del:                      34
% 2.70/0.99  res_num_eq_res_simplified:              0
% 2.70/0.99  res_num_sel_changes:                    0
% 2.70/0.99  res_moves_from_active_to_pass:          0
% 2.70/0.99  
% 2.70/0.99  ------ Superposition
% 2.70/0.99  
% 2.70/0.99  sup_time_total:                         0.
% 2.70/0.99  sup_time_generating:                    0.
% 2.70/0.99  sup_time_sim_full:                      0.
% 2.70/0.99  sup_time_sim_immed:                     0.
% 2.70/0.99  
% 2.70/0.99  sup_num_of_clauses:                     118
% 2.70/0.99  sup_num_in_active:                      56
% 2.70/0.99  sup_num_in_passive:                     62
% 2.70/0.99  sup_num_of_loops:                       64
% 2.70/0.99  sup_fw_superposition:                   65
% 2.70/0.99  sup_bw_superposition:                   63
% 2.70/0.99  sup_immediate_simplified:               4
% 2.70/0.99  sup_given_eliminated:                   0
% 2.70/0.99  comparisons_done:                       0
% 2.70/0.99  comparisons_avoided:                    0
% 2.70/0.99  
% 2.70/0.99  ------ Simplifications
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  sim_fw_subset_subsumed:                 0
% 2.70/0.99  sim_bw_subset_subsumed:                 4
% 2.70/0.99  sim_fw_subsumed:                        3
% 2.70/0.99  sim_bw_subsumed:                        0
% 2.70/0.99  sim_fw_subsumption_res:                 2
% 2.70/0.99  sim_bw_subsumption_res:                 0
% 2.70/0.99  sim_tautology_del:                      14
% 2.70/0.99  sim_eq_tautology_del:                   1
% 2.70/0.99  sim_eq_res_simp:                        2
% 2.70/0.99  sim_fw_demodulated:                     0
% 2.70/0.99  sim_bw_demodulated:                     7
% 2.70/0.99  sim_light_normalised:                   1
% 2.70/0.99  sim_joinable_taut:                      0
% 2.70/0.99  sim_joinable_simp:                      0
% 2.70/0.99  sim_ac_normalised:                      0
% 2.70/0.99  sim_smt_subsumption:                    0
% 2.70/0.99  
%------------------------------------------------------------------------------

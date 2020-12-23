%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:57 EST 2020

% Result     : Theorem 23.56s
% Output     : CNFRefutation 23.56s
% Verified   : 
% Statistics : Number of formulae       :  205 (6776 expanded)
%              Number of clauses        :  134 (2391 expanded)
%              Number of leaves         :   22 (1567 expanded)
%              Depth                    :   31
%              Number of atoms          :  630 (29323 expanded)
%              Number of equality atoms :  331 (10242 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
   => ( k2_relset_1(sK4,sK5,sK6) != sK5
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK6,X4) = X3
              & r2_hidden(X4,sK4) )
          | ~ r2_hidden(X3,sK5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f40,f39])).

fof(f71,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f69,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f14])).

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

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f72,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f78,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1217,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1220,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1614,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1220])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2090,plain,
    ( sK5 = k1_xboole_0
    | k1_relset_1(sK4,sK5,sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1614,c_34])).

cnf(c_2091,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2090])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1227,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2460,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1217,c_1227])).

cnf(c_2801,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2091,c_2460])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1229,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4823,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_1229])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1236,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1826,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_1236])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_207])).

cnf(c_270,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_208])).

cnf(c_1214,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_2211,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1826,c_1214])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1235,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2220,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2211,c_1235])).

cnf(c_31110,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4823,c_33,c_2220])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1240,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_31119,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_31110,c_1240])).

cnf(c_31128,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK4,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_31119,c_1240])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_8041,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8044,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8041])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1218,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3525,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1240])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1241,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1219,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2448,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1219])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1226,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2284,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1217,c_1226])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2600,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2284,c_1228])).

cnf(c_35,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2974,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2600,c_35])).

cnf(c_2979,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2974,c_1236])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1239,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3292,plain,
    ( k2_relat_1(sK6) = sK5
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2979,c_1239])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1565,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_551,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1542,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_2009,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_1667,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3099,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(sK5,k2_relat_1(sK6))
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_3100,plain,
    ( sK5 = k2_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3099])).

cnf(c_9099,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3292,c_30,c_27,c_1565,c_2009,c_2979,c_3100])).

cnf(c_9104,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_2448,c_9099])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1231,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9469,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9104,c_1231])).

cnf(c_42267,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9469,c_33,c_2220])).

cnf(c_42273,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3525,c_42267])).

cnf(c_2561,plain,
    ( r2_hidden(sK0(sK5,X0),sK5)
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5530,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
    | r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_5531,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5530])).

cnf(c_42803,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42273,c_30,c_27,c_1565,c_2009,c_2979,c_3100,c_5531])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1242,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_42809,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_42803,c_1242])).

cnf(c_47062,plain,
    ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42809,c_30,c_27,c_1565,c_2009,c_2979,c_3100])).

cnf(c_47067,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_47062])).

cnf(c_55828,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31128,c_8044,c_47067])).

cnf(c_55995,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_55828,c_1217])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1224,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_58221,plain,
    ( sK6 = k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_55995,c_1224])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_98,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_102,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_550,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1729,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_1636,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | X0 = sK6 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1889,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_1890,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1905,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_1906,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2057,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_2058,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_563,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1592,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK6
    | X2 != sK5
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_1728,plain,
    ( v1_funct_2(X0,sK4,X1)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK6
    | X1 != sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_3067,plain,
    ( v1_funct_2(sK6,sK4,X0)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK5
    | sK6 != sK6
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_3068,plain,
    ( X0 != sK5
    | sK6 != sK6
    | sK4 != sK4
    | v1_funct_2(sK6,sK4,X0) = iProver_top
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3067])).

cnf(c_3070,plain,
    ( sK6 != sK6
    | sK4 != sK4
    | k1_xboole_0 != sK5
    | v1_funct_2(sK6,sK4,sK5) != iProver_top
    | v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3068])).

cnf(c_1673,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_2552,plain,
    ( k2_relat_1(sK6) != X0
    | sK5 != X0
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_3444,plain,
    ( k2_relat_1(sK6) != k2_relat_1(X0)
    | sK5 != k2_relat_1(X0)
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_3446,plain,
    ( k2_relat_1(sK6) != k2_relat_1(k1_xboole_0)
    | sK5 = k2_relat_1(sK6)
    | sK5 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3444])).

cnf(c_557,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_3445,plain,
    ( k2_relat_1(sK6) = k2_relat_1(X0)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_557])).

cnf(c_3447,plain,
    ( k2_relat_1(sK6) = k2_relat_1(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3445])).

cnf(c_3639,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(X0) = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_3640,plain,
    ( k2_relat_1(k1_xboole_0) = sK5
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3639])).

cnf(c_5312,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_20206,plain,
    ( k2_relat_1(X0) != sK5
    | sK5 = k2_relat_1(X0)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_5312])).

cnf(c_20217,plain,
    ( k2_relat_1(k1_xboole_0) != sK5
    | sK5 = k2_relat_1(k1_xboole_0)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_20206])).

cnf(c_60235,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_58221,c_34,c_30,c_27,c_10,c_98,c_102,c_1565,c_1729,c_1889,c_1890,c_1905,c_1906,c_2009,c_2058,c_3070,c_3446,c_3447,c_3640,c_8044,c_20217,c_47067])).

cnf(c_60245,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_60235,c_47062])).

cnf(c_55988,plain,
    ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_55828,c_2460])).

cnf(c_60241,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_60235,c_55988])).

cnf(c_60243,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_60235,c_55995])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1221,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_60789,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_60243,c_1221])).

cnf(c_1216,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_55996,plain,
    ( v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_55828,c_1216])).

cnf(c_60244,plain,
    ( v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_60235,c_55996])).

cnf(c_65571,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_60789,c_60244])).

cnf(c_88075,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_60241,c_65571])).

cnf(c_88440,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_60245,c_88075])).

cnf(c_1238,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_88442,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_88440,c_1238])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.56/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.56/3.50  
% 23.56/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.56/3.50  
% 23.56/3.50  ------  iProver source info
% 23.56/3.50  
% 23.56/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.56/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.56/3.50  git: non_committed_changes: false
% 23.56/3.50  git: last_make_outside_of_git: false
% 23.56/3.50  
% 23.56/3.50  ------ 
% 23.56/3.50  ------ Parsing...
% 23.56/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.56/3.50  
% 23.56/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.56/3.50  
% 23.56/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.56/3.50  
% 23.56/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.56/3.50  ------ Proving...
% 23.56/3.50  ------ Problem Properties 
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  clauses                                 32
% 23.56/3.50  conjectures                             6
% 23.56/3.50  EPR                                     6
% 23.56/3.50  Horn                                    25
% 23.56/3.50  unary                                   8
% 23.56/3.50  binary                                  9
% 23.56/3.50  lits                                    84
% 23.56/3.50  lits eq                                 22
% 23.56/3.50  fd_pure                                 0
% 23.56/3.50  fd_pseudo                               0
% 23.56/3.50  fd_cond                                 3
% 23.56/3.50  fd_pseudo_cond                          4
% 23.56/3.50  AC symbols                              0
% 23.56/3.50  
% 23.56/3.50  ------ Input Options Time Limit: Unbounded
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  ------ 
% 23.56/3.50  Current options:
% 23.56/3.50  ------ 
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  ------ Proving...
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  % SZS status Theorem for theBenchmark.p
% 23.56/3.50  
% 23.56/3.50   Resolution empty clause
% 23.56/3.50  
% 23.56/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.56/3.50  
% 23.56/3.50  fof(f12,conjecture,(
% 23.56/3.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f13,negated_conjecture,(
% 23.56/3.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 23.56/3.50    inference(negated_conjecture,[],[f12])).
% 23.56/3.50  
% 23.56/3.50  fof(f23,plain,(
% 23.56/3.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 23.56/3.50    inference(ennf_transformation,[],[f13])).
% 23.56/3.50  
% 23.56/3.50  fof(f24,plain,(
% 23.56/3.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 23.56/3.50    inference(flattening,[],[f23])).
% 23.56/3.50  
% 23.56/3.50  fof(f40,plain,(
% 23.56/3.50    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 23.56/3.50    introduced(choice_axiom,[])).
% 23.56/3.50  
% 23.56/3.50  fof(f39,plain,(
% 23.56/3.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 23.56/3.50    introduced(choice_axiom,[])).
% 23.56/3.50  
% 23.56/3.50  fof(f41,plain,(
% 23.56/3.50    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 23.56/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f40,f39])).
% 23.56/3.50  
% 23.56/3.50  fof(f71,plain,(
% 23.56/3.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 23.56/3.50    inference(cnf_transformation,[],[f41])).
% 23.56/3.50  
% 23.56/3.50  fof(f11,axiom,(
% 23.56/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f21,plain,(
% 23.56/3.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.56/3.50    inference(ennf_transformation,[],[f11])).
% 23.56/3.50  
% 23.56/3.50  fof(f22,plain,(
% 23.56/3.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.56/3.50    inference(flattening,[],[f21])).
% 23.56/3.50  
% 23.56/3.50  fof(f38,plain,(
% 23.56/3.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.56/3.50    inference(nnf_transformation,[],[f22])).
% 23.56/3.50  
% 23.56/3.50  fof(f63,plain,(
% 23.56/3.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f38])).
% 23.56/3.50  
% 23.56/3.50  fof(f70,plain,(
% 23.56/3.50    v1_funct_2(sK6,sK4,sK5)),
% 23.56/3.50    inference(cnf_transformation,[],[f41])).
% 23.56/3.50  
% 23.56/3.50  fof(f9,axiom,(
% 23.56/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f19,plain,(
% 23.56/3.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.56/3.50    inference(ennf_transformation,[],[f9])).
% 23.56/3.50  
% 23.56/3.50  fof(f61,plain,(
% 23.56/3.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f19])).
% 23.56/3.50  
% 23.56/3.50  fof(f7,axiom,(
% 23.56/3.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f16,plain,(
% 23.56/3.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.56/3.50    inference(ennf_transformation,[],[f7])).
% 23.56/3.50  
% 23.56/3.50  fof(f17,plain,(
% 23.56/3.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.56/3.50    inference(flattening,[],[f16])).
% 23.56/3.50  
% 23.56/3.50  fof(f32,plain,(
% 23.56/3.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.56/3.50    inference(nnf_transformation,[],[f17])).
% 23.56/3.50  
% 23.56/3.50  fof(f33,plain,(
% 23.56/3.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.56/3.50    inference(rectify,[],[f32])).
% 23.56/3.50  
% 23.56/3.50  fof(f36,plain,(
% 23.56/3.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 23.56/3.50    introduced(choice_axiom,[])).
% 23.56/3.50  
% 23.56/3.50  fof(f35,plain,(
% 23.56/3.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 23.56/3.50    introduced(choice_axiom,[])).
% 23.56/3.50  
% 23.56/3.50  fof(f34,plain,(
% 23.56/3.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 23.56/3.50    introduced(choice_axiom,[])).
% 23.56/3.50  
% 23.56/3.50  fof(f37,plain,(
% 23.56/3.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.56/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f36,f35,f34])).
% 23.56/3.50  
% 23.56/3.50  fof(f54,plain,(
% 23.56/3.50    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f37])).
% 23.56/3.50  
% 23.56/3.50  fof(f80,plain,(
% 23.56/3.50    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.56/3.50    inference(equality_resolution,[],[f54])).
% 23.56/3.50  
% 23.56/3.50  fof(f69,plain,(
% 23.56/3.50    v1_funct_1(sK6)),
% 23.56/3.50    inference(cnf_transformation,[],[f41])).
% 23.56/3.50  
% 23.56/3.50  fof(f3,axiom,(
% 23.56/3.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f31,plain,(
% 23.56/3.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.56/3.50    inference(nnf_transformation,[],[f3])).
% 23.56/3.50  
% 23.56/3.50  fof(f48,plain,(
% 23.56/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f31])).
% 23.56/3.50  
% 23.56/3.50  fof(f4,axiom,(
% 23.56/3.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f15,plain,(
% 23.56/3.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 23.56/3.50    inference(ennf_transformation,[],[f4])).
% 23.56/3.50  
% 23.56/3.50  fof(f50,plain,(
% 23.56/3.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f15])).
% 23.56/3.50  
% 23.56/3.50  fof(f49,plain,(
% 23.56/3.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f31])).
% 23.56/3.50  
% 23.56/3.50  fof(f5,axiom,(
% 23.56/3.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f51,plain,(
% 23.56/3.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f5])).
% 23.56/3.50  
% 23.56/3.50  fof(f1,axiom,(
% 23.56/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f14,plain,(
% 23.56/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.56/3.50    inference(ennf_transformation,[],[f1])).
% 23.56/3.50  
% 23.56/3.50  fof(f25,plain,(
% 23.56/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.56/3.50    inference(nnf_transformation,[],[f14])).
% 23.56/3.50  
% 23.56/3.50  fof(f26,plain,(
% 23.56/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.56/3.50    inference(rectify,[],[f25])).
% 23.56/3.50  
% 23.56/3.50  fof(f27,plain,(
% 23.56/3.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.56/3.50    introduced(choice_axiom,[])).
% 23.56/3.50  
% 23.56/3.50  fof(f28,plain,(
% 23.56/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.56/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 23.56/3.50  
% 23.56/3.50  fof(f42,plain,(
% 23.56/3.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f28])).
% 23.56/3.50  
% 23.56/3.50  fof(f2,axiom,(
% 23.56/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f29,plain,(
% 23.56/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.56/3.50    inference(nnf_transformation,[],[f2])).
% 23.56/3.50  
% 23.56/3.50  fof(f30,plain,(
% 23.56/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.56/3.50    inference(flattening,[],[f29])).
% 23.56/3.50  
% 23.56/3.50  fof(f45,plain,(
% 23.56/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.56/3.50    inference(cnf_transformation,[],[f30])).
% 23.56/3.50  
% 23.56/3.50  fof(f76,plain,(
% 23.56/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.56/3.50    inference(equality_resolution,[],[f45])).
% 23.56/3.50  
% 23.56/3.50  fof(f72,plain,(
% 23.56/3.50    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f41])).
% 23.56/3.50  
% 23.56/3.50  fof(f43,plain,(
% 23.56/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f28])).
% 23.56/3.50  
% 23.56/3.50  fof(f73,plain,(
% 23.56/3.50    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f41])).
% 23.56/3.50  
% 23.56/3.50  fof(f10,axiom,(
% 23.56/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f20,plain,(
% 23.56/3.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.56/3.50    inference(ennf_transformation,[],[f10])).
% 23.56/3.50  
% 23.56/3.50  fof(f62,plain,(
% 23.56/3.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f20])).
% 23.56/3.50  
% 23.56/3.50  fof(f8,axiom,(
% 23.56/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f18,plain,(
% 23.56/3.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.56/3.50    inference(ennf_transformation,[],[f8])).
% 23.56/3.50  
% 23.56/3.50  fof(f60,plain,(
% 23.56/3.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f18])).
% 23.56/3.50  
% 23.56/3.50  fof(f47,plain,(
% 23.56/3.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f30])).
% 23.56/3.50  
% 23.56/3.50  fof(f74,plain,(
% 23.56/3.50    k2_relset_1(sK4,sK5,sK6) != sK5),
% 23.56/3.50    inference(cnf_transformation,[],[f41])).
% 23.56/3.50  
% 23.56/3.50  fof(f56,plain,(
% 23.56/3.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f37])).
% 23.56/3.50  
% 23.56/3.50  fof(f77,plain,(
% 23.56/3.50    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.56/3.50    inference(equality_resolution,[],[f56])).
% 23.56/3.50  
% 23.56/3.50  fof(f78,plain,(
% 23.56/3.50    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.56/3.50    inference(equality_resolution,[],[f77])).
% 23.56/3.50  
% 23.56/3.50  fof(f44,plain,(
% 23.56/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 23.56/3.50    inference(cnf_transformation,[],[f28])).
% 23.56/3.50  
% 23.56/3.50  fof(f67,plain,(
% 23.56/3.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f38])).
% 23.56/3.50  
% 23.56/3.50  fof(f83,plain,(
% 23.56/3.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 23.56/3.50    inference(equality_resolution,[],[f67])).
% 23.56/3.50  
% 23.56/3.50  fof(f6,axiom,(
% 23.56/3.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 23.56/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.56/3.50  
% 23.56/3.50  fof(f53,plain,(
% 23.56/3.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 23.56/3.50    inference(cnf_transformation,[],[f6])).
% 23.56/3.50  
% 23.56/3.50  fof(f64,plain,(
% 23.56/3.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.56/3.50    inference(cnf_transformation,[],[f38])).
% 23.56/3.50  
% 23.56/3.50  fof(f85,plain,(
% 23.56/3.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 23.56/3.50    inference(equality_resolution,[],[f64])).
% 23.56/3.50  
% 23.56/3.50  cnf(c_30,negated_conjecture,
% 23.56/3.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 23.56/3.50      inference(cnf_transformation,[],[f71]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1217,plain,
% 23.56/3.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_26,plain,
% 23.56/3.50      ( ~ v1_funct_2(X0,X1,X2)
% 23.56/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | k1_relset_1(X1,X2,X0) = X1
% 23.56/3.50      | k1_xboole_0 = X2 ),
% 23.56/3.50      inference(cnf_transformation,[],[f63]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1220,plain,
% 23.56/3.50      ( k1_relset_1(X0,X1,X2) = X0
% 23.56/3.50      | k1_xboole_0 = X1
% 23.56/3.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 23.56/3.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1614,plain,
% 23.56/3.50      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 23.56/3.50      | sK5 = k1_xboole_0
% 23.56/3.50      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1217,c_1220]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_31,negated_conjecture,
% 23.56/3.50      ( v1_funct_2(sK6,sK4,sK5) ),
% 23.56/3.50      inference(cnf_transformation,[],[f70]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_34,plain,
% 23.56/3.50      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2090,plain,
% 23.56/3.50      ( sK5 = k1_xboole_0 | k1_relset_1(sK4,sK5,sK6) = sK4 ),
% 23.56/3.50      inference(global_propositional_subsumption,[status(thm)],[c_1614,c_34]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2091,plain,
% 23.56/3.50      ( k1_relset_1(sK4,sK5,sK6) = sK4 | sK5 = k1_xboole_0 ),
% 23.56/3.50      inference(renaming,[status(thm)],[c_2090]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_19,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f61]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1227,plain,
% 23.56/3.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.56/3.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2460,plain,
% 23.56/3.50      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1217,c_1227]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2801,plain,
% 23.56/3.50      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_2091,c_2460]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_17,plain,
% 23.56/3.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 23.56/3.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 23.56/3.50      | ~ v1_funct_1(X1)
% 23.56/3.50      | ~ v1_relat_1(X1) ),
% 23.56/3.50      inference(cnf_transformation,[],[f80]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1229,plain,
% 23.56/3.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 23.56/3.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 23.56/3.50      | v1_funct_1(X1) != iProver_top
% 23.56/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_4823,plain,
% 23.56/3.50      ( sK5 = k1_xboole_0
% 23.56/3.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 23.56/3.50      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
% 23.56/3.50      | v1_funct_1(sK6) != iProver_top
% 23.56/3.50      | v1_relat_1(sK6) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_2801,c_1229]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_32,negated_conjecture,
% 23.56/3.50      ( v1_funct_1(sK6) ),
% 23.56/3.50      inference(cnf_transformation,[],[f69]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_33,plain,
% 23.56/3.50      ( v1_funct_1(sK6) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_7,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.56/3.50      inference(cnf_transformation,[],[f48]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1236,plain,
% 23.56/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.56/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1826,plain,
% 23.56/3.50      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1217,c_1236]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_8,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f50]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_6,plain,
% 23.56/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.56/3.50      inference(cnf_transformation,[],[f49]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_207,plain,
% 23.56/3.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 23.56/3.50      inference(prop_impl,[status(thm)],[c_6]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_208,plain,
% 23.56/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.56/3.50      inference(renaming,[status(thm)],[c_207]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_270,plain,
% 23.56/3.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 23.56/3.50      inference(bin_hyper_res,[status(thm)],[c_8,c_208]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1214,plain,
% 23.56/3.50      ( r1_tarski(X0,X1) != iProver_top
% 23.56/3.50      | v1_relat_1(X1) != iProver_top
% 23.56/3.50      | v1_relat_1(X0) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2211,plain,
% 23.56/3.50      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 23.56/3.50      | v1_relat_1(sK6) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1826,c_1214]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_9,plain,
% 23.56/3.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 23.56/3.50      inference(cnf_transformation,[],[f51]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1235,plain,
% 23.56/3.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2220,plain,
% 23.56/3.50      ( v1_relat_1(sK6) = iProver_top ),
% 23.56/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_2211,c_1235]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_31110,plain,
% 23.56/3.50      ( sK5 = k1_xboole_0
% 23.56/3.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 23.56/3.50      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_4823,c_33,c_2220]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2,plain,
% 23.56/3.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 23.56/3.50      inference(cnf_transformation,[],[f42]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1240,plain,
% 23.56/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.56/3.50      | r2_hidden(X0,X2) = iProver_top
% 23.56/3.50      | r1_tarski(X1,X2) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_31119,plain,
% 23.56/3.50      ( sK5 = k1_xboole_0
% 23.56/3.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 23.56/3.50      | r2_hidden(sK3(sK6,X0),X1) = iProver_top
% 23.56/3.50      | r1_tarski(sK4,X1) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_31110,c_1240]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_31128,plain,
% 23.56/3.50      ( sK5 = k1_xboole_0
% 23.56/3.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 23.56/3.50      | r2_hidden(sK3(sK6,X0),X1) = iProver_top
% 23.56/3.50      | r1_tarski(X2,X1) != iProver_top
% 23.56/3.50      | r1_tarski(sK4,X2) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_31119,c_1240]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f76]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_8041,plain,
% 23.56/3.50      ( r1_tarski(sK4,sK4) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_8044,plain,
% 23.56/3.50      ( r1_tarski(sK4,sK4) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_8041]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_29,negated_conjecture,
% 23.56/3.50      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 23.56/3.50      inference(cnf_transformation,[],[f72]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1218,plain,
% 23.56/3.50      ( r2_hidden(X0,sK5) != iProver_top
% 23.56/3.50      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3525,plain,
% 23.56/3.50      ( r2_hidden(X0,sK5) != iProver_top
% 23.56/3.50      | r2_hidden(sK7(X0),X1) = iProver_top
% 23.56/3.50      | r1_tarski(sK4,X1) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1218,c_1240]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1,plain,
% 23.56/3.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.56/3.50      inference(cnf_transformation,[],[f43]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1241,plain,
% 23.56/3.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 23.56/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_28,negated_conjecture,
% 23.56/3.50      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 23.56/3.50      inference(cnf_transformation,[],[f73]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1219,plain,
% 23.56/3.50      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2448,plain,
% 23.56/3.50      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 23.56/3.50      | r1_tarski(sK5,X0) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1241,c_1219]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_20,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 23.56/3.50      inference(cnf_transformation,[],[f62]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1226,plain,
% 23.56/3.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 23.56/3.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2284,plain,
% 23.56/3.50      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_1217,c_1226]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_18,plain,
% 23.56/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.56/3.50      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 23.56/3.50      inference(cnf_transformation,[],[f60]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1228,plain,
% 23.56/3.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.56/3.50      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2600,plain,
% 23.56/3.50      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
% 23.56/3.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_2284,c_1228]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_35,plain,
% 23.56/3.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2974,plain,
% 23.56/3.50      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
% 23.56/3.50      inference(global_propositional_subsumption,[status(thm)],[c_2600,c_35]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2979,plain,
% 23.56/3.50      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_2974,c_1236]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3,plain,
% 23.56/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 23.56/3.50      inference(cnf_transformation,[],[f47]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1239,plain,
% 23.56/3.50      ( X0 = X1
% 23.56/3.50      | r1_tarski(X1,X0) != iProver_top
% 23.56/3.50      | r1_tarski(X0,X1) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3292,plain,
% 23.56/3.50      ( k2_relat_1(sK6) = sK5 | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_2979,c_1239]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_27,negated_conjecture,
% 23.56/3.50      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 23.56/3.50      inference(cnf_transformation,[],[f74]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1565,plain,
% 23.56/3.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 23.56/3.50      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_20]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_551,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1542,plain,
% 23.56/3.50      ( k2_relset_1(sK4,sK5,sK6) != X0
% 23.56/3.50      | k2_relset_1(sK4,sK5,sK6) = sK5
% 23.56/3.50      | sK5 != X0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_551]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2009,plain,
% 23.56/3.50      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 23.56/3.50      | k2_relset_1(sK4,sK5,sK6) = sK5
% 23.56/3.50      | sK5 != k2_relat_1(sK6) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1542]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1667,plain,
% 23.56/3.50      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3099,plain,
% 23.56/3.50      ( ~ r1_tarski(k2_relat_1(sK6),sK5)
% 23.56/3.50      | ~ r1_tarski(sK5,k2_relat_1(sK6))
% 23.56/3.50      | sK5 = k2_relat_1(sK6) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1667]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3100,plain,
% 23.56/3.50      ( sK5 = k2_relat_1(sK6)
% 23.56/3.50      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
% 23.56/3.50      | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_3099]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_9099,plain,
% 23.56/3.50      ( r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_3292,c_30,c_27,c_1565,c_2009,c_2979,c_3100]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_9104,plain,
% 23.56/3.50      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_2448,c_9099]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_15,plain,
% 23.56/3.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 23.56/3.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 23.56/3.50      | ~ v1_funct_1(X1)
% 23.56/3.50      | ~ v1_relat_1(X1) ),
% 23.56/3.50      inference(cnf_transformation,[],[f78]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1231,plain,
% 23.56/3.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 23.56/3.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 23.56/3.50      | v1_funct_1(X1) != iProver_top
% 23.56/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_9469,plain,
% 23.56/3.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 23.56/3.50      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top
% 23.56/3.50      | v1_funct_1(sK6) != iProver_top
% 23.56/3.50      | v1_relat_1(sK6) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_9104,c_1231]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_42267,plain,
% 23.56/3.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 23.56/3.50      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_9469,c_33,c_2220]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_42273,plain,
% 23.56/3.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 23.56/3.50      | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
% 23.56/3.50      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_3525,c_42267]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2561,plain,
% 23.56/3.50      ( r2_hidden(sK0(sK5,X0),sK5) | r1_tarski(sK5,X0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_5530,plain,
% 23.56/3.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
% 23.56/3.50      | r1_tarski(sK5,k2_relat_1(sK6)) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_2561]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_5531,plain,
% 23.56/3.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
% 23.56/3.50      | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_5530]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_42803,plain,
% 23.56/3.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 23.56/3.50      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_42273,c_30,c_27,c_1565,c_2009,c_2979,c_3100,c_5531]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_0,plain,
% 23.56/3.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 23.56/3.50      inference(cnf_transformation,[],[f44]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1242,plain,
% 23.56/3.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 23.56/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_42809,plain,
% 23.56/3.50      ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
% 23.56/3.50      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_42803,c_1242]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_47062,plain,
% 23.56/3.50      ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_42809,c_30,c_27,c_1565,c_2009,c_2979,c_3100]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_47067,plain,
% 23.56/3.50      ( sK5 = k1_xboole_0 | r1_tarski(sK4,sK4) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_2801,c_47062]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_55828,plain,
% 23.56/3.50      ( sK5 = k1_xboole_0 ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_31128,c_8044,c_47067]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_55995,plain,
% 23.56/3.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 23.56/3.50      inference(demodulation,[status(thm)],[c_55828,c_1217]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_22,plain,
% 23.56/3.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 23.56/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 23.56/3.50      | k1_xboole_0 = X1
% 23.56/3.50      | k1_xboole_0 = X0 ),
% 23.56/3.50      inference(cnf_transformation,[],[f83]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1224,plain,
% 23.56/3.50      ( k1_xboole_0 = X0
% 23.56/3.50      | k1_xboole_0 = X1
% 23.56/3.50      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 23.56/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_58221,plain,
% 23.56/3.50      ( sK6 = k1_xboole_0
% 23.56/3.50      | sK4 = k1_xboole_0
% 23.56/3.50      | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_55995,c_1224]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_10,plain,
% 23.56/3.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 23.56/3.50      inference(cnf_transformation,[],[f53]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_98,plain,
% 23.56/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_102,plain,
% 23.56/3.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_550,plain,( X0 = X0 ),theory(equality) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1729,plain,
% 23.56/3.50      ( sK4 = sK4 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_550]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1636,plain,
% 23.56/3.50      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | X0 = sK6 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1889,plain,
% 23.56/3.50      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1636]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1890,plain,
% 23.56/3.50      ( r1_tarski(sK6,sK6) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1905,plain,
% 23.56/3.50      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1667]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1906,plain,
% 23.56/3.50      ( r1_tarski(sK5,sK5) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2057,plain,
% 23.56/3.50      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_551]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2058,plain,
% 23.56/3.50      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_2057]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_563,plain,
% 23.56/3.50      ( ~ v1_funct_2(X0,X1,X2)
% 23.56/3.50      | v1_funct_2(X3,X4,X5)
% 23.56/3.50      | X3 != X0
% 23.56/3.50      | X4 != X1
% 23.56/3.50      | X5 != X2 ),
% 23.56/3.50      theory(equality) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1592,plain,
% 23.56/3.50      ( v1_funct_2(X0,X1,X2)
% 23.56/3.50      | ~ v1_funct_2(sK6,sK4,sK5)
% 23.56/3.50      | X0 != sK6
% 23.56/3.50      | X2 != sK5
% 23.56/3.50      | X1 != sK4 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_563]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1728,plain,
% 23.56/3.50      ( v1_funct_2(X0,sK4,X1)
% 23.56/3.50      | ~ v1_funct_2(sK6,sK4,sK5)
% 23.56/3.50      | X0 != sK6
% 23.56/3.50      | X1 != sK5
% 23.56/3.50      | sK4 != sK4 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1592]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3067,plain,
% 23.56/3.50      ( v1_funct_2(sK6,sK4,X0)
% 23.56/3.50      | ~ v1_funct_2(sK6,sK4,sK5)
% 23.56/3.50      | X0 != sK5
% 23.56/3.50      | sK6 != sK6
% 23.56/3.50      | sK4 != sK4 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1728]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3068,plain,
% 23.56/3.50      ( X0 != sK5
% 23.56/3.50      | sK6 != sK6
% 23.56/3.50      | sK4 != sK4
% 23.56/3.50      | v1_funct_2(sK6,sK4,X0) = iProver_top
% 23.56/3.50      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_3067]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3070,plain,
% 23.56/3.50      ( sK6 != sK6
% 23.56/3.50      | sK4 != sK4
% 23.56/3.50      | k1_xboole_0 != sK5
% 23.56/3.50      | v1_funct_2(sK6,sK4,sK5) != iProver_top
% 23.56/3.50      | v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_3068]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1673,plain,
% 23.56/3.50      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_551]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_2552,plain,
% 23.56/3.50      ( k2_relat_1(sK6) != X0 | sK5 != X0 | sK5 = k2_relat_1(sK6) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1673]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3444,plain,
% 23.56/3.50      ( k2_relat_1(sK6) != k2_relat_1(X0)
% 23.56/3.50      | sK5 != k2_relat_1(X0)
% 23.56/3.50      | sK5 = k2_relat_1(sK6) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_2552]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3446,plain,
% 23.56/3.50      ( k2_relat_1(sK6) != k2_relat_1(k1_xboole_0)
% 23.56/3.50      | sK5 = k2_relat_1(sK6)
% 23.56/3.50      | sK5 != k2_relat_1(k1_xboole_0) ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_3444]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_557,plain,
% 23.56/3.50      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 23.56/3.50      theory(equality) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3445,plain,
% 23.56/3.50      ( k2_relat_1(sK6) = k2_relat_1(X0) | sK6 != X0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_557]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3447,plain,
% 23.56/3.50      ( k2_relat_1(sK6) = k2_relat_1(k1_xboole_0) | sK6 != k1_xboole_0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_3445]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3639,plain,
% 23.56/3.50      ( k2_relat_1(X0) != X1 | k2_relat_1(X0) = sK5 | sK5 != X1 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_2057]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_3640,plain,
% 23.56/3.50      ( k2_relat_1(k1_xboole_0) = sK5
% 23.56/3.50      | k2_relat_1(k1_xboole_0) != k1_xboole_0
% 23.56/3.50      | sK5 != k1_xboole_0 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_3639]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_5312,plain,
% 23.56/3.50      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_1673]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_20206,plain,
% 23.56/3.50      ( k2_relat_1(X0) != sK5 | sK5 = k2_relat_1(X0) | sK5 != sK5 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_5312]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_20217,plain,
% 23.56/3.50      ( k2_relat_1(k1_xboole_0) != sK5
% 23.56/3.50      | sK5 = k2_relat_1(k1_xboole_0)
% 23.56/3.50      | sK5 != sK5 ),
% 23.56/3.50      inference(instantiation,[status(thm)],[c_20206]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_60235,plain,
% 23.56/3.50      ( sK4 = k1_xboole_0 ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_58221,c_34,c_30,c_27,c_10,c_98,c_102,c_1565,c_1729,c_1889,
% 23.56/3.50                 c_1890,c_1905,c_1906,c_2009,c_2058,c_3070,c_3446,c_3447,
% 23.56/3.50                 c_3640,c_8044,c_20217,c_47067]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_60245,plain,
% 23.56/3.50      ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) != iProver_top ),
% 23.56/3.50      inference(demodulation,[status(thm)],[c_60235,c_47062]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_55988,plain,
% 23.56/3.50      ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 23.56/3.50      inference(demodulation,[status(thm)],[c_55828,c_2460]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_60241,plain,
% 23.56/3.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 23.56/3.50      inference(demodulation,[status(thm)],[c_60235,c_55988]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_60243,plain,
% 23.56/3.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 23.56/3.50      inference(demodulation,[status(thm)],[c_60235,c_55995]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_25,plain,
% 23.56/3.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 23.56/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 23.56/3.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 23.56/3.50      inference(cnf_transformation,[],[f85]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1221,plain,
% 23.56/3.50      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 23.56/3.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 23.56/3.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_60789,plain,
% 23.56/3.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 23.56/3.50      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.56/3.50      inference(superposition,[status(thm)],[c_60243,c_1221]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1216,plain,
% 23.56/3.50      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_55996,plain,
% 23.56/3.50      ( v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
% 23.56/3.50      inference(demodulation,[status(thm)],[c_55828,c_1216]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_60244,plain,
% 23.56/3.50      ( v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.56/3.50      inference(demodulation,[status(thm)],[c_60235,c_55996]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_65571,plain,
% 23.56/3.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 23.56/3.50      inference(global_propositional_subsumption,
% 23.56/3.50                [status(thm)],
% 23.56/3.50                [c_60789,c_60244]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_88075,plain,
% 23.56/3.50      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 23.56/3.50      inference(light_normalisation,[status(thm)],[c_60241,c_65571]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_88440,plain,
% 23.56/3.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.56/3.50      inference(light_normalisation,[status(thm)],[c_60245,c_88075]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_1238,plain,
% 23.56/3.50      ( r1_tarski(X0,X0) = iProver_top ),
% 23.56/3.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.56/3.50  
% 23.56/3.50  cnf(c_88442,plain,
% 23.56/3.50      ( $false ),
% 23.56/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_88440,c_1238]) ).
% 23.56/3.50  
% 23.56/3.50  
% 23.56/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.56/3.50  
% 23.56/3.50  ------                               Statistics
% 23.56/3.50  
% 23.56/3.50  ------ Selected
% 23.56/3.50  
% 23.56/3.50  total_time:                             2.675
% 23.56/3.50  
%------------------------------------------------------------------------------

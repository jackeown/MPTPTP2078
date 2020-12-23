%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:49 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 863 expanded)
%              Number of clauses        :   79 ( 283 expanded)
%              Number of leaves         :   19 ( 201 expanded)
%              Depth                    :   21
%              Number of atoms          :  467 (3805 expanded)
%              Number of equality atoms :  201 (1156 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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

fof(f40,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f39,f38])).

fof(f68,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
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

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f15])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f74,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f65,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

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

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1312,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1322,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2734,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_1322])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1323,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1313,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1661,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1313])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1311,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1314,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1986,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1311,c_1314])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1316,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2193,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_1316])).

cnf(c_32,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2322,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2193,c_32])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1318,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2722,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_1318])).

cnf(c_2802,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_2722])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1324,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3883,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2802,c_1324])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1321,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3898,plain,
    ( k2_relat_1(sK6) = sK5
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3883,c_1321])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_911,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1361,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_1631,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_1421,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1814,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(sK5,k2_relat_1(sK6))
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_1815,plain,
    ( sK5 = k2_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_1968,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4765,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3898,c_27,c_24,c_1631,c_1815,c_1968,c_3883])).

cnf(c_4769,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_1661,c_4765])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_385,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_386,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_1306,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_387,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1389,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1524,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_1525,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1524])).

cnf(c_1584,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1306,c_32,c_387,c_1525])).

cnf(c_1585,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1584])).

cnf(c_5092,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4769,c_1585])).

cnf(c_5103,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_5092])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2892,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1686,plain,
    ( r2_hidden(sK0(X0,k2_relat_1(sK6)),X0)
    | r1_tarski(X0,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3650,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
    | r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1686])).

cnf(c_3654,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(c_3653,plain,
    ( ~ r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3656,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3653])).

cnf(c_3887,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3883])).

cnf(c_912,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1699,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK6))
    | r1_tarski(X1,k2_relat_1(sK6))
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_3856,plain,
    ( r1_tarski(X0,k2_relat_1(sK6))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK6))
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_4698,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK6))
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3856])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_619,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_621,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_27])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1315,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2035,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1311,c_1315])).

cnf(c_2273,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_621,c_2035])).

cnf(c_5104,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2273,c_5092])).

cnf(c_5408,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5103,c_27,c_24,c_1631,c_1814,c_1815,c_1968,c_2892,c_3654,c_3656,c_3883,c_3887,c_4698,c_5104])).

cnf(c_5412,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5408,c_1324])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5412,c_3883,c_1968,c_1815,c_1631,c_24,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:37:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.57/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.98  
% 3.57/0.98  ------  iProver source info
% 3.57/0.98  
% 3.57/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.98  git: non_committed_changes: false
% 3.57/0.98  git: last_make_outside_of_git: false
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  
% 3.57/0.98  ------ Input Options
% 3.57/0.98  
% 3.57/0.98  --out_options                           all
% 3.57/0.98  --tptp_safe_out                         true
% 3.57/0.98  --problem_path                          ""
% 3.57/0.98  --include_path                          ""
% 3.57/0.98  --clausifier                            res/vclausify_rel
% 3.57/0.98  --clausifier_options                    ""
% 3.57/0.98  --stdin                                 false
% 3.57/0.98  --stats_out                             all
% 3.57/0.98  
% 3.57/0.98  ------ General Options
% 3.57/0.98  
% 3.57/0.98  --fof                                   false
% 3.57/0.98  --time_out_real                         305.
% 3.57/0.98  --time_out_virtual                      -1.
% 3.57/0.98  --symbol_type_check                     false
% 3.57/0.98  --clausify_out                          false
% 3.57/0.98  --sig_cnt_out                           false
% 3.57/0.98  --trig_cnt_out                          false
% 3.57/0.98  --trig_cnt_out_tolerance                1.
% 3.57/0.98  --trig_cnt_out_sk_spl                   false
% 3.57/0.98  --abstr_cl_out                          false
% 3.57/0.98  
% 3.57/0.98  ------ Global Options
% 3.57/0.98  
% 3.57/0.98  --schedule                              default
% 3.57/0.98  --add_important_lit                     false
% 3.57/0.98  --prop_solver_per_cl                    1000
% 3.57/0.98  --min_unsat_core                        false
% 3.57/0.98  --soft_assumptions                      false
% 3.57/0.98  --soft_lemma_size                       3
% 3.57/0.98  --prop_impl_unit_size                   0
% 3.57/0.98  --prop_impl_unit                        []
% 3.57/0.98  --share_sel_clauses                     true
% 3.57/0.98  --reset_solvers                         false
% 3.57/0.98  --bc_imp_inh                            [conj_cone]
% 3.57/0.98  --conj_cone_tolerance                   3.
% 3.57/0.98  --extra_neg_conj                        none
% 3.57/0.98  --large_theory_mode                     true
% 3.57/0.98  --prolific_symb_bound                   200
% 3.57/0.98  --lt_threshold                          2000
% 3.57/0.98  --clause_weak_htbl                      true
% 3.57/0.98  --gc_record_bc_elim                     false
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing Options
% 3.57/0.98  
% 3.57/0.98  --preprocessing_flag                    true
% 3.57/0.98  --time_out_prep_mult                    0.1
% 3.57/0.98  --splitting_mode                        input
% 3.57/0.98  --splitting_grd                         true
% 3.57/0.98  --splitting_cvd                         false
% 3.57/0.98  --splitting_cvd_svl                     false
% 3.57/0.98  --splitting_nvd                         32
% 3.57/0.98  --sub_typing                            true
% 3.57/0.98  --prep_gs_sim                           true
% 3.57/0.98  --prep_unflatten                        true
% 3.57/0.98  --prep_res_sim                          true
% 3.57/0.98  --prep_upred                            true
% 3.57/0.98  --prep_sem_filter                       exhaustive
% 3.57/0.98  --prep_sem_filter_out                   false
% 3.57/0.98  --pred_elim                             true
% 3.57/0.98  --res_sim_input                         true
% 3.57/0.98  --eq_ax_congr_red                       true
% 3.57/0.98  --pure_diseq_elim                       true
% 3.57/0.98  --brand_transform                       false
% 3.57/0.98  --non_eq_to_eq                          false
% 3.57/0.98  --prep_def_merge                        true
% 3.57/0.98  --prep_def_merge_prop_impl              false
% 3.57/0.98  --prep_def_merge_mbd                    true
% 3.57/0.98  --prep_def_merge_tr_red                 false
% 3.57/0.98  --prep_def_merge_tr_cl                  false
% 3.57/0.98  --smt_preprocessing                     true
% 3.57/0.98  --smt_ac_axioms                         fast
% 3.57/0.98  --preprocessed_out                      false
% 3.57/0.98  --preprocessed_stats                    false
% 3.57/0.98  
% 3.57/0.98  ------ Abstraction refinement Options
% 3.57/0.98  
% 3.57/0.98  --abstr_ref                             []
% 3.57/0.98  --abstr_ref_prep                        false
% 3.57/0.98  --abstr_ref_until_sat                   false
% 3.57/0.98  --abstr_ref_sig_restrict                funpre
% 3.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.98  --abstr_ref_under                       []
% 3.57/0.98  
% 3.57/0.98  ------ SAT Options
% 3.57/0.98  
% 3.57/0.98  --sat_mode                              false
% 3.57/0.98  --sat_fm_restart_options                ""
% 3.57/0.98  --sat_gr_def                            false
% 3.57/0.98  --sat_epr_types                         true
% 3.57/0.98  --sat_non_cyclic_types                  false
% 3.57/0.98  --sat_finite_models                     false
% 3.57/0.98  --sat_fm_lemmas                         false
% 3.57/0.98  --sat_fm_prep                           false
% 3.57/0.98  --sat_fm_uc_incr                        true
% 3.57/0.98  --sat_out_model                         small
% 3.57/0.98  --sat_out_clauses                       false
% 3.57/0.98  
% 3.57/0.98  ------ QBF Options
% 3.57/0.98  
% 3.57/0.98  --qbf_mode                              false
% 3.57/0.98  --qbf_elim_univ                         false
% 3.57/0.98  --qbf_dom_inst                          none
% 3.57/0.98  --qbf_dom_pre_inst                      false
% 3.57/0.98  --qbf_sk_in                             false
% 3.57/0.98  --qbf_pred_elim                         true
% 3.57/0.98  --qbf_split                             512
% 3.57/0.98  
% 3.57/0.98  ------ BMC1 Options
% 3.57/0.98  
% 3.57/0.98  --bmc1_incremental                      false
% 3.57/0.98  --bmc1_axioms                           reachable_all
% 3.57/0.98  --bmc1_min_bound                        0
% 3.57/0.98  --bmc1_max_bound                        -1
% 3.57/0.98  --bmc1_max_bound_default                -1
% 3.57/0.98  --bmc1_symbol_reachability              true
% 3.57/0.98  --bmc1_property_lemmas                  false
% 3.57/0.98  --bmc1_k_induction                      false
% 3.57/0.98  --bmc1_non_equiv_states                 false
% 3.57/0.98  --bmc1_deadlock                         false
% 3.57/0.98  --bmc1_ucm                              false
% 3.57/0.98  --bmc1_add_unsat_core                   none
% 3.57/0.98  --bmc1_unsat_core_children              false
% 3.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.98  --bmc1_out_stat                         full
% 3.57/0.98  --bmc1_ground_init                      false
% 3.57/0.98  --bmc1_pre_inst_next_state              false
% 3.57/0.98  --bmc1_pre_inst_state                   false
% 3.57/0.98  --bmc1_pre_inst_reach_state             false
% 3.57/0.98  --bmc1_out_unsat_core                   false
% 3.57/0.98  --bmc1_aig_witness_out                  false
% 3.57/0.98  --bmc1_verbose                          false
% 3.57/0.98  --bmc1_dump_clauses_tptp                false
% 3.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.98  --bmc1_dump_file                        -
% 3.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.98  --bmc1_ucm_extend_mode                  1
% 3.57/0.98  --bmc1_ucm_init_mode                    2
% 3.57/0.98  --bmc1_ucm_cone_mode                    none
% 3.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.98  --bmc1_ucm_relax_model                  4
% 3.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.98  --bmc1_ucm_layered_model                none
% 3.57/0.98  --bmc1_ucm_max_lemma_size               10
% 3.57/0.98  
% 3.57/0.98  ------ AIG Options
% 3.57/0.98  
% 3.57/0.98  --aig_mode                              false
% 3.57/0.98  
% 3.57/0.98  ------ Instantiation Options
% 3.57/0.98  
% 3.57/0.98  --instantiation_flag                    true
% 3.57/0.98  --inst_sos_flag                         true
% 3.57/0.98  --inst_sos_phase                        true
% 3.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel_side                     num_symb
% 3.57/0.98  --inst_solver_per_active                1400
% 3.57/0.98  --inst_solver_calls_frac                1.
% 3.57/0.98  --inst_passive_queue_type               priority_queues
% 3.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.98  --inst_passive_queues_freq              [25;2]
% 3.57/0.98  --inst_dismatching                      true
% 3.57/0.98  --inst_eager_unprocessed_to_passive     true
% 3.57/0.98  --inst_prop_sim_given                   true
% 3.57/0.98  --inst_prop_sim_new                     false
% 3.57/0.98  --inst_subs_new                         false
% 3.57/0.98  --inst_eq_res_simp                      false
% 3.57/0.98  --inst_subs_given                       false
% 3.57/0.98  --inst_orphan_elimination               true
% 3.57/0.98  --inst_learning_loop_flag               true
% 3.57/0.98  --inst_learning_start                   3000
% 3.57/0.98  --inst_learning_factor                  2
% 3.57/0.98  --inst_start_prop_sim_after_learn       3
% 3.57/0.98  --inst_sel_renew                        solver
% 3.57/0.98  --inst_lit_activity_flag                true
% 3.57/0.98  --inst_restr_to_given                   false
% 3.57/0.98  --inst_activity_threshold               500
% 3.57/0.98  --inst_out_proof                        true
% 3.57/0.98  
% 3.57/0.98  ------ Resolution Options
% 3.57/0.98  
% 3.57/0.98  --resolution_flag                       true
% 3.57/0.98  --res_lit_sel                           adaptive
% 3.57/0.98  --res_lit_sel_side                      none
% 3.57/0.98  --res_ordering                          kbo
% 3.57/0.98  --res_to_prop_solver                    active
% 3.57/0.98  --res_prop_simpl_new                    false
% 3.57/0.98  --res_prop_simpl_given                  true
% 3.57/0.98  --res_passive_queue_type                priority_queues
% 3.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.98  --res_passive_queues_freq               [15;5]
% 3.57/0.98  --res_forward_subs                      full
% 3.57/0.98  --res_backward_subs                     full
% 3.57/0.98  --res_forward_subs_resolution           true
% 3.57/0.98  --res_backward_subs_resolution          true
% 3.57/0.98  --res_orphan_elimination                true
% 3.57/0.98  --res_time_limit                        2.
% 3.57/0.98  --res_out_proof                         true
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Options
% 3.57/0.98  
% 3.57/0.98  --superposition_flag                    true
% 3.57/0.98  --sup_passive_queue_type                priority_queues
% 3.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.98  --demod_completeness_check              fast
% 3.57/0.98  --demod_use_ground                      true
% 3.57/0.98  --sup_to_prop_solver                    passive
% 3.57/0.98  --sup_prop_simpl_new                    true
% 3.57/0.98  --sup_prop_simpl_given                  true
% 3.57/0.98  --sup_fun_splitting                     true
% 3.57/0.98  --sup_smt_interval                      50000
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Simplification Setup
% 3.57/0.98  
% 3.57/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.57/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.57/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.57/0.98  --sup_immed_triv                        [TrivRules]
% 3.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_immed_bw_main                     []
% 3.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_input_bw                          []
% 3.57/0.98  
% 3.57/0.98  ------ Combination Options
% 3.57/0.98  
% 3.57/0.98  --comb_res_mult                         3
% 3.57/0.98  --comb_sup_mult                         2
% 3.57/0.98  --comb_inst_mult                        10
% 3.57/0.98  
% 3.57/0.98  ------ Debug Options
% 3.57/0.98  
% 3.57/0.98  --dbg_backtrace                         false
% 3.57/0.98  --dbg_dump_prop_clauses                 false
% 3.57/0.98  --dbg_dump_prop_clauses_file            -
% 3.57/0.98  --dbg_out_stat                          false
% 3.57/0.98  ------ Parsing...
% 3.57/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.98  ------ Proving...
% 3.57/0.98  ------ Problem Properties 
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  clauses                                 24
% 3.57/0.98  conjectures                             4
% 3.57/0.98  EPR                                     4
% 3.57/0.98  Horn                                    19
% 3.57/0.98  unary                                   4
% 3.57/0.98  binary                                  9
% 3.57/0.98  lits                                    60
% 3.57/0.98  lits eq                                 18
% 3.57/0.98  fd_pure                                 0
% 3.57/0.98  fd_pseudo                               0
% 3.57/0.98  fd_cond                                 3
% 3.57/0.98  fd_pseudo_cond                          1
% 3.57/0.98  AC symbols                              0
% 3.57/0.98  
% 3.57/0.98  ------ Schedule dynamic 5 is on 
% 3.57/0.98  
% 3.57/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  Current options:
% 3.57/0.98  ------ 
% 3.57/0.98  
% 3.57/0.98  ------ Input Options
% 3.57/0.98  
% 3.57/0.98  --out_options                           all
% 3.57/0.98  --tptp_safe_out                         true
% 3.57/0.98  --problem_path                          ""
% 3.57/0.98  --include_path                          ""
% 3.57/0.98  --clausifier                            res/vclausify_rel
% 3.57/0.98  --clausifier_options                    ""
% 3.57/0.98  --stdin                                 false
% 3.57/0.98  --stats_out                             all
% 3.57/0.98  
% 3.57/0.98  ------ General Options
% 3.57/0.98  
% 3.57/0.98  --fof                                   false
% 3.57/0.98  --time_out_real                         305.
% 3.57/0.98  --time_out_virtual                      -1.
% 3.57/0.98  --symbol_type_check                     false
% 3.57/0.98  --clausify_out                          false
% 3.57/0.98  --sig_cnt_out                           false
% 3.57/0.98  --trig_cnt_out                          false
% 3.57/0.98  --trig_cnt_out_tolerance                1.
% 3.57/0.98  --trig_cnt_out_sk_spl                   false
% 3.57/0.98  --abstr_cl_out                          false
% 3.57/0.98  
% 3.57/0.98  ------ Global Options
% 3.57/0.98  
% 3.57/0.98  --schedule                              default
% 3.57/0.98  --add_important_lit                     false
% 3.57/0.98  --prop_solver_per_cl                    1000
% 3.57/0.98  --min_unsat_core                        false
% 3.57/0.98  --soft_assumptions                      false
% 3.57/0.98  --soft_lemma_size                       3
% 3.57/0.98  --prop_impl_unit_size                   0
% 3.57/0.98  --prop_impl_unit                        []
% 3.57/0.98  --share_sel_clauses                     true
% 3.57/0.98  --reset_solvers                         false
% 3.57/0.98  --bc_imp_inh                            [conj_cone]
% 3.57/0.98  --conj_cone_tolerance                   3.
% 3.57/0.98  --extra_neg_conj                        none
% 3.57/0.98  --large_theory_mode                     true
% 3.57/0.98  --prolific_symb_bound                   200
% 3.57/0.98  --lt_threshold                          2000
% 3.57/0.98  --clause_weak_htbl                      true
% 3.57/0.98  --gc_record_bc_elim                     false
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing Options
% 3.57/0.98  
% 3.57/0.98  --preprocessing_flag                    true
% 3.57/0.98  --time_out_prep_mult                    0.1
% 3.57/0.98  --splitting_mode                        input
% 3.57/0.98  --splitting_grd                         true
% 3.57/0.98  --splitting_cvd                         false
% 3.57/0.98  --splitting_cvd_svl                     false
% 3.57/0.98  --splitting_nvd                         32
% 3.57/0.98  --sub_typing                            true
% 3.57/0.98  --prep_gs_sim                           true
% 3.57/0.98  --prep_unflatten                        true
% 3.57/0.98  --prep_res_sim                          true
% 3.57/0.98  --prep_upred                            true
% 3.57/0.98  --prep_sem_filter                       exhaustive
% 3.57/0.98  --prep_sem_filter_out                   false
% 3.57/0.98  --pred_elim                             true
% 3.57/0.98  --res_sim_input                         true
% 3.57/0.98  --eq_ax_congr_red                       true
% 3.57/0.98  --pure_diseq_elim                       true
% 3.57/0.98  --brand_transform                       false
% 3.57/0.98  --non_eq_to_eq                          false
% 3.57/0.98  --prep_def_merge                        true
% 3.57/0.98  --prep_def_merge_prop_impl              false
% 3.57/0.98  --prep_def_merge_mbd                    true
% 3.57/0.98  --prep_def_merge_tr_red                 false
% 3.57/0.98  --prep_def_merge_tr_cl                  false
% 3.57/0.98  --smt_preprocessing                     true
% 3.57/0.98  --smt_ac_axioms                         fast
% 3.57/0.98  --preprocessed_out                      false
% 3.57/0.98  --preprocessed_stats                    false
% 3.57/0.98  
% 3.57/0.98  ------ Abstraction refinement Options
% 3.57/0.98  
% 3.57/0.98  --abstr_ref                             []
% 3.57/0.98  --abstr_ref_prep                        false
% 3.57/0.98  --abstr_ref_until_sat                   false
% 3.57/0.98  --abstr_ref_sig_restrict                funpre
% 3.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.98  --abstr_ref_under                       []
% 3.57/0.98  
% 3.57/0.98  ------ SAT Options
% 3.57/0.98  
% 3.57/0.98  --sat_mode                              false
% 3.57/0.98  --sat_fm_restart_options                ""
% 3.57/0.98  --sat_gr_def                            false
% 3.57/0.98  --sat_epr_types                         true
% 3.57/0.98  --sat_non_cyclic_types                  false
% 3.57/0.98  --sat_finite_models                     false
% 3.57/0.98  --sat_fm_lemmas                         false
% 3.57/0.98  --sat_fm_prep                           false
% 3.57/0.98  --sat_fm_uc_incr                        true
% 3.57/0.98  --sat_out_model                         small
% 3.57/0.98  --sat_out_clauses                       false
% 3.57/0.98  
% 3.57/0.98  ------ QBF Options
% 3.57/0.98  
% 3.57/0.98  --qbf_mode                              false
% 3.57/0.98  --qbf_elim_univ                         false
% 3.57/0.98  --qbf_dom_inst                          none
% 3.57/0.98  --qbf_dom_pre_inst                      false
% 3.57/0.98  --qbf_sk_in                             false
% 3.57/0.98  --qbf_pred_elim                         true
% 3.57/0.98  --qbf_split                             512
% 3.57/0.98  
% 3.57/0.98  ------ BMC1 Options
% 3.57/0.98  
% 3.57/0.98  --bmc1_incremental                      false
% 3.57/0.98  --bmc1_axioms                           reachable_all
% 3.57/0.98  --bmc1_min_bound                        0
% 3.57/0.98  --bmc1_max_bound                        -1
% 3.57/0.98  --bmc1_max_bound_default                -1
% 3.57/0.98  --bmc1_symbol_reachability              true
% 3.57/0.98  --bmc1_property_lemmas                  false
% 3.57/0.98  --bmc1_k_induction                      false
% 3.57/0.98  --bmc1_non_equiv_states                 false
% 3.57/0.98  --bmc1_deadlock                         false
% 3.57/0.98  --bmc1_ucm                              false
% 3.57/0.98  --bmc1_add_unsat_core                   none
% 3.57/0.98  --bmc1_unsat_core_children              false
% 3.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.98  --bmc1_out_stat                         full
% 3.57/0.98  --bmc1_ground_init                      false
% 3.57/0.98  --bmc1_pre_inst_next_state              false
% 3.57/0.98  --bmc1_pre_inst_state                   false
% 3.57/0.98  --bmc1_pre_inst_reach_state             false
% 3.57/0.98  --bmc1_out_unsat_core                   false
% 3.57/0.98  --bmc1_aig_witness_out                  false
% 3.57/0.98  --bmc1_verbose                          false
% 3.57/0.98  --bmc1_dump_clauses_tptp                false
% 3.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.98  --bmc1_dump_file                        -
% 3.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.98  --bmc1_ucm_extend_mode                  1
% 3.57/0.98  --bmc1_ucm_init_mode                    2
% 3.57/0.98  --bmc1_ucm_cone_mode                    none
% 3.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.98  --bmc1_ucm_relax_model                  4
% 3.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.98  --bmc1_ucm_layered_model                none
% 3.57/0.98  --bmc1_ucm_max_lemma_size               10
% 3.57/0.98  
% 3.57/0.98  ------ AIG Options
% 3.57/0.98  
% 3.57/0.98  --aig_mode                              false
% 3.57/0.98  
% 3.57/0.98  ------ Instantiation Options
% 3.57/0.98  
% 3.57/0.98  --instantiation_flag                    true
% 3.57/0.98  --inst_sos_flag                         true
% 3.57/0.98  --inst_sos_phase                        true
% 3.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel_side                     none
% 3.57/0.98  --inst_solver_per_active                1400
% 3.57/0.98  --inst_solver_calls_frac                1.
% 3.57/0.98  --inst_passive_queue_type               priority_queues
% 3.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.98  --inst_passive_queues_freq              [25;2]
% 3.57/0.98  --inst_dismatching                      true
% 3.57/0.98  --inst_eager_unprocessed_to_passive     true
% 3.57/0.98  --inst_prop_sim_given                   true
% 3.57/0.98  --inst_prop_sim_new                     false
% 3.57/0.98  --inst_subs_new                         false
% 3.57/0.98  --inst_eq_res_simp                      false
% 3.57/0.98  --inst_subs_given                       false
% 3.57/0.98  --inst_orphan_elimination               true
% 3.57/0.98  --inst_learning_loop_flag               true
% 3.57/0.98  --inst_learning_start                   3000
% 3.57/0.98  --inst_learning_factor                  2
% 3.57/0.98  --inst_start_prop_sim_after_learn       3
% 3.57/0.98  --inst_sel_renew                        solver
% 3.57/0.98  --inst_lit_activity_flag                true
% 3.57/0.98  --inst_restr_to_given                   false
% 3.57/0.98  --inst_activity_threshold               500
% 3.57/0.98  --inst_out_proof                        true
% 3.57/0.98  
% 3.57/0.98  ------ Resolution Options
% 3.57/0.98  
% 3.57/0.98  --resolution_flag                       false
% 3.57/0.98  --res_lit_sel                           adaptive
% 3.57/0.98  --res_lit_sel_side                      none
% 3.57/0.98  --res_ordering                          kbo
% 3.57/0.98  --res_to_prop_solver                    active
% 3.57/0.98  --res_prop_simpl_new                    false
% 3.57/0.98  --res_prop_simpl_given                  true
% 3.57/0.98  --res_passive_queue_type                priority_queues
% 3.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.98  --res_passive_queues_freq               [15;5]
% 3.57/0.98  --res_forward_subs                      full
% 3.57/0.98  --res_backward_subs                     full
% 3.57/0.98  --res_forward_subs_resolution           true
% 3.57/0.98  --res_backward_subs_resolution          true
% 3.57/0.98  --res_orphan_elimination                true
% 3.57/0.98  --res_time_limit                        2.
% 3.57/0.98  --res_out_proof                         true
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Options
% 3.57/0.98  
% 3.57/0.98  --superposition_flag                    true
% 3.57/0.98  --sup_passive_queue_type                priority_queues
% 3.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.98  --demod_completeness_check              fast
% 3.57/0.98  --demod_use_ground                      true
% 3.57/0.98  --sup_to_prop_solver                    passive
% 3.57/0.98  --sup_prop_simpl_new                    true
% 3.57/0.98  --sup_prop_simpl_given                  true
% 3.57/0.98  --sup_fun_splitting                     true
% 3.57/0.98  --sup_smt_interval                      50000
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Simplification Setup
% 3.57/0.98  
% 3.57/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.57/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.57/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.57/0.98  --sup_immed_triv                        [TrivRules]
% 3.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_immed_bw_main                     []
% 3.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_input_bw                          []
% 3.57/0.98  
% 3.57/0.98  ------ Combination Options
% 3.57/0.98  
% 3.57/0.98  --comb_res_mult                         3
% 3.57/0.98  --comb_sup_mult                         2
% 3.57/0.98  --comb_inst_mult                        10
% 3.57/0.98  
% 3.57/0.98  ------ Debug Options
% 3.57/0.98  
% 3.57/0.98  --dbg_backtrace                         false
% 3.57/0.98  --dbg_dump_prop_clauses                 false
% 3.57/0.98  --dbg_dump_prop_clauses_file            -
% 3.57/0.98  --dbg_out_stat                          false
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ Proving...
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  % SZS status Theorem for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  fof(f11,conjecture,(
% 3.57/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f12,negated_conjecture,(
% 3.57/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.57/0.98    inference(negated_conjecture,[],[f11])).
% 3.57/0.98  
% 3.57/0.98  fof(f23,plain,(
% 3.57/0.98    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.57/0.98    inference(ennf_transformation,[],[f12])).
% 3.57/0.98  
% 3.57/0.98  fof(f24,plain,(
% 3.57/0.98    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.57/0.98    inference(flattening,[],[f23])).
% 3.57/0.98  
% 3.57/0.98  fof(f39,plain,(
% 3.57/0.98    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f38,plain,(
% 3.57/0.98    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f40,plain,(
% 3.57/0.98    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f39,f38])).
% 3.57/0.98  
% 3.57/0.98  fof(f68,plain,(
% 3.57/0.98    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f40])).
% 3.57/0.98  
% 3.57/0.98  fof(f1,axiom,(
% 3.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f13,plain,(
% 3.57/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f1])).
% 3.57/0.98  
% 3.57/0.98  fof(f25,plain,(
% 3.57/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/0.98    inference(nnf_transformation,[],[f13])).
% 3.57/0.98  
% 3.57/0.98  fof(f26,plain,(
% 3.57/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/0.98    inference(rectify,[],[f25])).
% 3.57/0.98  
% 3.57/0.98  fof(f27,plain,(
% 3.57/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f28,plain,(
% 3.57/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.57/0.98  
% 3.57/0.98  fof(f41,plain,(
% 3.57/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f28])).
% 3.57/0.98  
% 3.57/0.98  fof(f42,plain,(
% 3.57/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f28])).
% 3.57/0.98  
% 3.57/0.98  fof(f69,plain,(
% 3.57/0.98    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f40])).
% 3.57/0.98  
% 3.57/0.98  fof(f67,plain,(
% 3.57/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.57/0.98    inference(cnf_transformation,[],[f40])).
% 3.57/0.98  
% 3.57/0.98  fof(f9,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f20,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(ennf_transformation,[],[f9])).
% 3.57/0.98  
% 3.57/0.98  fof(f58,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f20])).
% 3.57/0.98  
% 3.57/0.98  fof(f7,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f18,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(ennf_transformation,[],[f7])).
% 3.57/0.98  
% 3.57/0.98  fof(f56,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f18])).
% 3.57/0.98  
% 3.57/0.98  fof(f4,axiom,(
% 3.57/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f14,plain,(
% 3.57/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f4])).
% 3.57/0.98  
% 3.57/0.98  fof(f48,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f14])).
% 3.57/0.98  
% 3.57/0.98  fof(f43,plain,(
% 3.57/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f28])).
% 3.57/0.98  
% 3.57/0.98  fof(f2,axiom,(
% 3.57/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f29,plain,(
% 3.57/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/0.98    inference(nnf_transformation,[],[f2])).
% 3.57/0.98  
% 3.57/0.98  fof(f30,plain,(
% 3.57/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/0.98    inference(flattening,[],[f29])).
% 3.57/0.98  
% 3.57/0.98  fof(f46,plain,(
% 3.57/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f30])).
% 3.57/0.98  
% 3.57/0.98  fof(f70,plain,(
% 3.57/0.98    k2_relset_1(sK4,sK5,sK6) != sK5),
% 3.57/0.98    inference(cnf_transformation,[],[f40])).
% 3.57/0.98  
% 3.57/0.98  fof(f5,axiom,(
% 3.57/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f15,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f5])).
% 3.57/0.98  
% 3.57/0.98  fof(f16,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.98    inference(flattening,[],[f15])).
% 3.57/0.98  
% 3.57/0.98  fof(f31,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.98    inference(nnf_transformation,[],[f16])).
% 3.57/0.98  
% 3.57/0.98  fof(f32,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.98    inference(rectify,[],[f31])).
% 3.57/0.98  
% 3.57/0.98  fof(f35,plain,(
% 3.57/0.98    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f34,plain,(
% 3.57/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f33,plain,(
% 3.57/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f36,plain,(
% 3.57/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).
% 3.57/0.98  
% 3.57/0.98  fof(f51,plain,(
% 3.57/0.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f36])).
% 3.57/0.98  
% 3.57/0.98  fof(f73,plain,(
% 3.57/0.98    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.98    inference(equality_resolution,[],[f51])).
% 3.57/0.98  
% 3.57/0.98  fof(f74,plain,(
% 3.57/0.98    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.57/0.98    inference(equality_resolution,[],[f73])).
% 3.57/0.98  
% 3.57/0.98  fof(f65,plain,(
% 3.57/0.98    v1_funct_1(sK6)),
% 3.57/0.98    inference(cnf_transformation,[],[f40])).
% 3.57/0.98  
% 3.57/0.98  fof(f6,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f17,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(ennf_transformation,[],[f6])).
% 3.57/0.98  
% 3.57/0.98  fof(f55,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f17])).
% 3.57/0.98  
% 3.57/0.98  fof(f3,axiom,(
% 3.57/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f47,plain,(
% 3.57/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.57/0.98    inference(cnf_transformation,[],[f3])).
% 3.57/0.98  
% 3.57/0.98  fof(f10,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f21,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(ennf_transformation,[],[f10])).
% 3.57/0.98  
% 3.57/0.98  fof(f22,plain,(
% 3.57/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(flattening,[],[f21])).
% 3.57/0.98  
% 3.57/0.98  fof(f37,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(nnf_transformation,[],[f22])).
% 3.57/0.98  
% 3.57/0.98  fof(f59,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f37])).
% 3.57/0.98  
% 3.57/0.98  fof(f66,plain,(
% 3.57/0.98    v1_funct_2(sK6,sK4,sK5)),
% 3.57/0.98    inference(cnf_transformation,[],[f40])).
% 3.57/0.98  
% 3.57/0.98  fof(f8,axiom,(
% 3.57/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.57/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f19,plain,(
% 3.57/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.98    inference(ennf_transformation,[],[f8])).
% 3.57/0.98  
% 3.57/0.98  fof(f57,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.98    inference(cnf_transformation,[],[f19])).
% 3.57/0.98  
% 3.57/0.98  cnf(c_26,negated_conjecture,
% 3.57/0.98      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 3.57/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1312,plain,
% 3.57/0.98      ( r2_hidden(X0,sK5) != iProver_top
% 3.57/0.98      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.57/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1322,plain,
% 3.57/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.57/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.57/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2734,plain,
% 3.57/0.98      ( r2_hidden(X0,sK5) != iProver_top
% 3.57/0.98      | r2_hidden(sK7(X0),X1) = iProver_top
% 3.57/0.98      | r1_tarski(sK4,X1) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1312,c_1322]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1,plain,
% 3.57/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1323,plain,
% 3.57/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.57/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_25,negated_conjecture,
% 3.57/0.98      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 3.57/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1313,plain,
% 3.57/0.98      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1661,plain,
% 3.57/0.98      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 3.57/0.98      | r1_tarski(sK5,X0) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1323,c_1313]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_27,negated_conjecture,
% 3.57/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.57/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1311,plain,
% 3.57/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_17,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1314,plain,
% 3.57/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1986,plain,
% 3.57/0.98      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1311,c_1314]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_15,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1316,plain,
% 3.57/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.57/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2193,plain,
% 3.57/0.98      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
% 3.57/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1986,c_1316]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_32,plain,
% 3.57/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2322,plain,
% 3.57/0.98      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_2193,c_32]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_7,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.57/0.98      | ~ r2_hidden(X2,X0)
% 3.57/0.98      | r2_hidden(X2,X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1318,plain,
% 3.57/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.57/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.57/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2722,plain,
% 3.57/0.98      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.57/0.98      | r2_hidden(X0,sK5) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2322,c_1318]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2802,plain,
% 3.57/0.98      ( r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top
% 3.57/0.98      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1323,c_2722]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_0,plain,
% 3.57/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1324,plain,
% 3.57/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.57/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3883,plain,
% 3.57/0.98      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2802,c_1324]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3,plain,
% 3.57/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.57/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1321,plain,
% 3.57/0.98      ( X0 = X1
% 3.57/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.57/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3898,plain,
% 3.57/0.98      ( k2_relat_1(sK6) = sK5
% 3.57/0.98      | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3883,c_1321]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_24,negated_conjecture,
% 3.57/0.98      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 3.57/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_911,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1361,plain,
% 3.57/0.98      ( k2_relset_1(sK4,sK5,sK6) != X0
% 3.57/0.98      | k2_relset_1(sK4,sK5,sK6) = sK5
% 3.57/0.98      | sK5 != X0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_911]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1631,plain,
% 3.57/0.98      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 3.57/0.98      | k2_relset_1(sK4,sK5,sK6) = sK5
% 3.57/0.98      | sK5 != k2_relat_1(sK6) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1361]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1421,plain,
% 3.57/0.98      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1814,plain,
% 3.57/0.98      ( ~ r1_tarski(k2_relat_1(sK6),sK5)
% 3.57/0.98      | ~ r1_tarski(sK5,k2_relat_1(sK6))
% 3.57/0.98      | sK5 = k2_relat_1(sK6) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1421]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1815,plain,
% 3.57/0.98      ( sK5 = k2_relat_1(sK6)
% 3.57/0.98      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
% 3.57/0.98      | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1814]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1968,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.57/0.98      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4765,plain,
% 3.57/0.98      ( r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3898,c_27,c_24,c_1631,c_1815,c_1968,c_3883]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4769,plain,
% 3.57/0.98      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1661,c_4765]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_11,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.57/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.57/0.98      | ~ v1_relat_1(X1)
% 3.57/0.98      | ~ v1_funct_1(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_29,negated_conjecture,
% 3.57/0.98      ( v1_funct_1(sK6) ),
% 3.57/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_385,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.57/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.57/0.98      | ~ v1_relat_1(X1)
% 3.57/0.98      | sK6 != X1 ),
% 3.57/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_386,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.57/0.98      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 3.57/0.98      | ~ v1_relat_1(sK6) ),
% 3.57/0.98      inference(unflattening,[status(thm)],[c_385]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1306,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.57/0.98      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.57/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_387,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.57/0.98      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.57/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_14,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | v1_relat_1(X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1389,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.57/0.98      | v1_relat_1(sK6) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1524,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.57/0.98      | v1_relat_1(sK6) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1389]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1525,plain,
% 3.57/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.57/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_1524]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1584,plain,
% 3.57/0.99      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.57/0.99      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_1306,c_32,c_387,c_1525]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1585,plain,
% 3.57/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.57/0.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_1584]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5092,plain,
% 3.57/0.99      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 3.57/0.99      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_4769,c_1585]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5103,plain,
% 3.57/0.99      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 3.57/0.99      | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
% 3.57/0.99      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2734,c_5092]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6,plain,
% 3.57/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2892,plain,
% 3.57/0.99      ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1686,plain,
% 3.57/0.99      ( r2_hidden(sK0(X0,k2_relat_1(sK6)),X0)
% 3.57/0.99      | r1_tarski(X0,k2_relat_1(sK6)) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3650,plain,
% 3.57/0.99      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
% 3.57/0.99      | r1_tarski(sK5,k2_relat_1(sK6)) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_1686]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3654,plain,
% 3.57/0.99      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
% 3.57/0.99      | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_3650]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3653,plain,
% 3.57/0.99      ( ~ r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
% 3.57/0.99      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),sK4) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3656,plain,
% 3.57/0.99      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
% 3.57/0.99      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),sK4) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_3653]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3887,plain,
% 3.57/0.99      ( r1_tarski(k2_relat_1(sK6),sK5) ),
% 3.57/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3883]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_912,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.57/0.99      theory(equality) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1699,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,k2_relat_1(sK6))
% 3.57/0.99      | r1_tarski(X1,k2_relat_1(sK6))
% 3.57/0.99      | X1 != X0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_912]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3856,plain,
% 3.57/0.99      ( r1_tarski(X0,k2_relat_1(sK6))
% 3.57/0.99      | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK6))
% 3.57/0.99      | X0 != k1_xboole_0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_1699]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4698,plain,
% 3.57/0.99      ( r1_tarski(sK5,k2_relat_1(sK6))
% 3.57/0.99      | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK6))
% 3.57/0.99      | sK5 != k1_xboole_0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_3856]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_23,plain,
% 3.57/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.57/0.99      | k1_xboole_0 = X2 ),
% 3.57/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_28,negated_conjecture,
% 3.57/0.99      ( v1_funct_2(sK6,sK4,sK5) ),
% 3.57/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_618,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.57/0.99      | sK6 != X0
% 3.57/0.99      | sK5 != X2
% 3.57/0.99      | sK4 != X1
% 3.57/0.99      | k1_xboole_0 = X2 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_619,plain,
% 3.57/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.57/0.99      | k1_relset_1(sK4,sK5,sK6) = sK4
% 3.57/0.99      | k1_xboole_0 = sK5 ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_618]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_621,plain,
% 3.57/0.99      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_619,c_27]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_16,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1315,plain,
% 3.57/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.57/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2035,plain,
% 3.57/0.99      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_1311,c_1315]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2273,plain,
% 3.57/0.99      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_621,c_2035]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5104,plain,
% 3.57/0.99      ( sK5 = k1_xboole_0
% 3.57/0.99      | r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 3.57/0.99      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),sK4) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2273,c_5092]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5408,plain,
% 3.57/0.99      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_5103,c_27,c_24,c_1631,c_1814,c_1815,c_1968,c_2892,
% 3.57/0.99                 c_3654,c_3656,c_3883,c_3887,c_4698,c_5104]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5412,plain,
% 3.57/0.99      ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_5408,c_1324]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(contradiction,plain,
% 3.57/0.99      ( $false ),
% 3.57/0.99      inference(minisat,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_5412,c_3883,c_1968,c_1815,c_1631,c_24,c_27]) ).
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  ------                               Statistics
% 3.57/0.99  
% 3.57/0.99  ------ General
% 3.57/0.99  
% 3.57/0.99  abstr_ref_over_cycles:                  0
% 3.57/0.99  abstr_ref_under_cycles:                 0
% 3.57/0.99  gc_basic_clause_elim:                   0
% 3.57/0.99  forced_gc_time:                         0
% 3.57/0.99  parsing_time:                           0.006
% 3.57/0.99  unif_index_cands_time:                  0.
% 3.57/0.99  unif_index_add_time:                    0.
% 3.57/0.99  orderings_time:                         0.
% 3.57/0.99  out_proof_time:                         0.008
% 3.57/0.99  total_time:                             0.144
% 3.57/0.99  num_of_symbols:                         53
% 3.57/0.99  num_of_terms:                           5130
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing
% 3.57/0.99  
% 3.57/0.99  num_of_splits:                          0
% 3.57/0.99  num_of_split_atoms:                     0
% 3.57/0.99  num_of_reused_defs:                     0
% 3.57/0.99  num_eq_ax_congr_red:                    29
% 3.57/0.99  num_of_sem_filtered_clauses:            1
% 3.57/0.99  num_of_subtypes:                        0
% 3.57/0.99  monotx_restored_types:                  0
% 3.57/0.99  sat_num_of_epr_types:                   0
% 3.57/0.99  sat_num_of_non_cyclic_types:            0
% 3.57/0.99  sat_guarded_non_collapsed_types:        0
% 3.57/0.99  num_pure_diseq_elim:                    0
% 3.57/0.99  simp_replaced_by:                       0
% 3.57/0.99  res_preprocessed:                       134
% 3.57/0.99  prep_upred:                             0
% 3.57/0.99  prep_unflattend:                        45
% 3.57/0.99  smt_new_axioms:                         0
% 3.57/0.99  pred_elim_cands:                        4
% 3.57/0.99  pred_elim:                              2
% 3.57/0.99  pred_elim_cl:                           5
% 3.57/0.99  pred_elim_cycles:                       5
% 3.57/0.99  merged_defs:                            0
% 3.57/0.99  merged_defs_ncl:                        0
% 3.57/0.99  bin_hyper_res:                          0
% 3.57/0.99  prep_cycles:                            4
% 3.57/0.99  pred_elim_time:                         0.006
% 3.57/0.99  splitting_time:                         0.
% 3.57/0.99  sem_filter_time:                        0.
% 3.57/0.99  monotx_time:                            0.
% 3.57/0.99  subtype_inf_time:                       0.
% 3.57/0.99  
% 3.57/0.99  ------ Problem properties
% 3.57/0.99  
% 3.57/0.99  clauses:                                24
% 3.57/0.99  conjectures:                            4
% 3.57/0.99  epr:                                    4
% 3.57/0.99  horn:                                   19
% 3.57/0.99  ground:                                 5
% 3.57/0.99  unary:                                  4
% 3.57/0.99  binary:                                 9
% 3.57/0.99  lits:                                   60
% 3.57/0.99  lits_eq:                                18
% 3.57/0.99  fd_pure:                                0
% 3.57/0.99  fd_pseudo:                              0
% 3.57/0.99  fd_cond:                                3
% 3.57/0.99  fd_pseudo_cond:                         1
% 3.57/0.99  ac_symbols:                             0
% 3.57/0.99  
% 3.57/0.99  ------ Propositional Solver
% 3.57/0.99  
% 3.57/0.99  prop_solver_calls:                      31
% 3.57/0.99  prop_fast_solver_calls:                 968
% 3.57/0.99  smt_solver_calls:                       0
% 3.57/0.99  smt_fast_solver_calls:                  0
% 3.57/0.99  prop_num_of_clauses:                    2471
% 3.57/0.99  prop_preprocess_simplified:             6754
% 3.57/0.99  prop_fo_subsumed:                       12
% 3.57/0.99  prop_solver_time:                       0.
% 3.57/0.99  smt_solver_time:                        0.
% 3.57/0.99  smt_fast_solver_time:                   0.
% 3.57/0.99  prop_fast_solver_time:                  0.
% 3.57/0.99  prop_unsat_core_time:                   0.
% 3.57/0.99  
% 3.57/0.99  ------ QBF
% 3.57/0.99  
% 3.57/0.99  qbf_q_res:                              0
% 3.57/0.99  qbf_num_tautologies:                    0
% 3.57/0.99  qbf_prep_cycles:                        0
% 3.57/0.99  
% 3.57/0.99  ------ BMC1
% 3.57/0.99  
% 3.57/0.99  bmc1_current_bound:                     -1
% 3.57/0.99  bmc1_last_solved_bound:                 -1
% 3.57/0.99  bmc1_unsat_core_size:                   -1
% 3.57/0.99  bmc1_unsat_core_parents_size:           -1
% 3.57/0.99  bmc1_merge_next_fun:                    0
% 3.57/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation
% 3.57/0.99  
% 3.57/0.99  inst_num_of_clauses:                    653
% 3.57/0.99  inst_num_in_passive:                    260
% 3.57/0.99  inst_num_in_active:                     254
% 3.57/0.99  inst_num_in_unprocessed:                139
% 3.57/0.99  inst_num_of_loops:                      360
% 3.57/0.99  inst_num_of_learning_restarts:          0
% 3.57/0.99  inst_num_moves_active_passive:          102
% 3.57/0.99  inst_lit_activity:                      0
% 3.57/0.99  inst_lit_activity_moves:                0
% 3.57/0.99  inst_num_tautologies:                   0
% 3.57/0.99  inst_num_prop_implied:                  0
% 3.57/0.99  inst_num_existing_simplified:           0
% 3.57/0.99  inst_num_eq_res_simplified:             0
% 3.57/0.99  inst_num_child_elim:                    0
% 3.57/0.99  inst_num_of_dismatching_blockings:      99
% 3.57/0.99  inst_num_of_non_proper_insts:           485
% 3.57/0.99  inst_num_of_duplicates:                 0
% 3.57/0.99  inst_inst_num_from_inst_to_res:         0
% 3.57/0.99  inst_dismatching_checking_time:         0.
% 3.57/0.99  
% 3.57/0.99  ------ Resolution
% 3.57/0.99  
% 3.57/0.99  res_num_of_clauses:                     0
% 3.57/0.99  res_num_in_passive:                     0
% 3.57/0.99  res_num_in_active:                      0
% 3.57/0.99  res_num_of_loops:                       138
% 3.57/0.99  res_forward_subset_subsumed:            29
% 3.57/0.99  res_backward_subset_subsumed:           0
% 3.57/0.99  res_forward_subsumed:                   0
% 3.57/0.99  res_backward_subsumed:                  0
% 3.57/0.99  res_forward_subsumption_resolution:     0
% 3.57/0.99  res_backward_subsumption_resolution:    0
% 3.57/0.99  res_clause_to_clause_subsumption:       540
% 3.57/0.99  res_orphan_elimination:                 0
% 3.57/0.99  res_tautology_del:                      52
% 3.57/0.99  res_num_eq_res_simplified:              0
% 3.57/0.99  res_num_sel_changes:                    0
% 3.57/0.99  res_moves_from_active_to_pass:          0
% 3.57/0.99  
% 3.57/0.99  ------ Superposition
% 3.57/0.99  
% 3.57/0.99  sup_time_total:                         0.
% 3.57/0.99  sup_time_generating:                    0.
% 3.57/0.99  sup_time_sim_full:                      0.
% 3.57/0.99  sup_time_sim_immed:                     0.
% 3.57/0.99  
% 3.57/0.99  sup_num_of_clauses:                     194
% 3.57/0.99  sup_num_in_active:                      70
% 3.57/0.99  sup_num_in_passive:                     124
% 3.57/0.99  sup_num_of_loops:                       71
% 3.57/0.99  sup_fw_superposition:                   134
% 3.57/0.99  sup_bw_superposition:                   87
% 3.57/0.99  sup_immediate_simplified:               21
% 3.57/0.99  sup_given_eliminated:                   0
% 3.57/0.99  comparisons_done:                       0
% 3.57/0.99  comparisons_avoided:                    10
% 3.57/0.99  
% 3.57/0.99  ------ Simplifications
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  sim_fw_subset_subsumed:                 14
% 3.57/0.99  sim_bw_subset_subsumed:                 2
% 3.57/0.99  sim_fw_subsumed:                        5
% 3.57/0.99  sim_bw_subsumed:                        1
% 3.57/0.99  sim_fw_subsumption_res:                 0
% 3.57/0.99  sim_bw_subsumption_res:                 0
% 3.57/0.99  sim_tautology_del:                      1
% 3.57/0.99  sim_eq_tautology_del:                   15
% 3.57/0.99  sim_eq_res_simp:                        0
% 3.57/0.99  sim_fw_demodulated:                     2
% 3.57/0.99  sim_bw_demodulated:                     1
% 3.57/0.99  sim_light_normalised:                   0
% 3.57/0.99  sim_joinable_taut:                      0
% 3.57/0.99  sim_joinable_simp:                      0
% 3.57/0.99  sim_ac_normalised:                      0
% 3.57/0.99  sim_smt_subsumption:                    0
% 3.57/0.99  
%------------------------------------------------------------------------------

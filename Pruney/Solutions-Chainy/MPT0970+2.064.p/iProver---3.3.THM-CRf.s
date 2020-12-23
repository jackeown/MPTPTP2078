%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:58 EST 2020

% Result     : Theorem 31.59s
% Output     : CNFRefutation 31.59s
% Verified   : 
% Statistics : Number of formulae       :  225 (1965 expanded)
%              Number of clauses        :  154 ( 741 expanded)
%              Number of leaves         :   21 ( 500 expanded)
%              Depth                    :   20
%              Number of atoms          :  789 (9770 expanded)
%              Number of equality atoms :  378 (3455 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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

fof(f43,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f42,f41])).

fof(f71,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f81,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12025,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X1)
    | r2_hidden(sK1(sK6,X0),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_29470,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),X0)
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_12025])).

cnf(c_119491,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_29470])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_608,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_609,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_1872,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_610,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1875,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1883,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2345,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_1883])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_256,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_257,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_256])).

cnf(c_320,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_257])).

cnf(c_2249,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_2377,plain,
    ( ~ r1_tarski(sK6,k2_zfmisc_1(X0,X1))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2249])).

cnf(c_2477,plain,
    ( ~ r1_tarski(sK6,k2_zfmisc_1(sK4,sK5))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2377])).

cnf(c_2478,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2477])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2514,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2515,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2514])).

cnf(c_2764,plain,
    ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | k2_relat_1(sK6) = X0
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1872,c_610,c_2345,c_2478,c_2515])).

cnf(c_2765,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2764])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1877,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2774,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_2765,c_1877])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2198,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1233,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2258,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_1234,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2256,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2316,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2256])).

cnf(c_2598,plain,
    ( k2_relat_1(sK6) != sK5
    | sK5 = k2_relat_1(sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2316])).

cnf(c_2149,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2823,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_3430,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2774,c_30,c_27,c_2198,c_2258,c_2598,c_2823])).

cnf(c_3431,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(renaming,[status(thm)],[c_3430])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_692,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_32])).

cnf(c_693,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_1867,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_694,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_2519,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1867,c_694,c_2345,c_2478,c_2515])).

cnf(c_2520,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_2519])).

cnf(c_1885,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3550,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),X1) = iProver_top
    | r1_tarski(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2520,c_1885])).

cnf(c_5073,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(k4_tarski(sK7(sK1(sK6,sK5)),sK1(sK6,sK5)),X0) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_3550])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_70,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1264,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_2314,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2315,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2314])).

cnf(c_2346,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2345])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1886,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1887,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2870,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_1887])).

cnf(c_2878,plain,
    ( r1_tarski(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2870])).

cnf(c_2880,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2878])).

cnf(c_3253,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_3255,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3253])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3369,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3370,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3369])).

cnf(c_1235,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3689,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK6,X2),X2)
    | X1 != X2
    | X0 != sK1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_12130,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | r2_hidden(k1_funct_1(sK6,sK7(sK1(sK6,sK5))),X0)
    | X0 != sK5
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_3689])).

cnf(c_23822,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | r2_hidden(k1_funct_1(sK6,sK7(sK1(sK6,sK5))),sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_12130])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_725,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_32])).

cnf(c_726,plain,
    ( r2_hidden(X0,k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_1865,plain,
    ( k1_funct_1(sK6,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_727,plain,
    ( k1_funct_1(sK6,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_2630,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | k1_funct_1(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1865,c_727,c_2345,c_2478,c_2515])).

cnf(c_2631,plain,
    ( k1_funct_1(sK6,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2630])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_671,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_672,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,X1),X1)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,X1) != k1_funct_1(sK6,X0)
    | k2_relat_1(sK6) = X1 ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_1868,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_673,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_2619,plain,
    ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | k2_relat_1(sK6) = X0
    | sK1(sK6,X0) != k1_funct_1(sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1868,c_673,c_2345,c_2478,c_2515])).

cnf(c_2620,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2619])).

cnf(c_3436,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_2620])).

cnf(c_3374,plain,
    ( sK1(sK6,X0) != X1
    | sK1(sK6,X0) = k1_funct_1(sK6,X2)
    | k1_funct_1(sK6,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_4493,plain,
    ( sK1(sK6,X0) != sK1(sK6,X0)
    | sK1(sK6,X0) = k1_funct_1(sK6,X1)
    | k1_funct_1(sK6,X1) != sK1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3374])).

cnf(c_8980,plain,
    ( sK1(sK6,sK5) != sK1(sK6,sK5)
    | sK1(sK6,sK5) = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_4493])).

cnf(c_4494,plain,
    ( sK1(sK6,X0) = sK1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_11395,plain,
    ( sK1(sK6,sK5) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_4494])).

cnf(c_25868,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_25869,plain,
    ( sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25868])).

cnf(c_28845,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3436,c_30,c_27,c_2198,c_2258,c_2345,c_2478,c_2515,c_2598,c_2823,c_3255,c_3431,c_8980,c_11395,c_25869])).

cnf(c_28851,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2631,c_28845])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_826,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_827,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_829,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_30])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1879,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2952,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1875,c_1879])).

cnf(c_3184,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_829,c_2952])).

cnf(c_28853,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | sK5 = k1_xboole_0
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3184,c_28845])).

cnf(c_53126,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_funct_1(sK6,sK7(sK1(sK6,sK5))),sK5)
    | X0 != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_53136,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK7(sK1(sK6,sK5))),sK5)
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_53126])).

cnf(c_58187,plain,
    ( X0 != X1
    | X0 = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != X1 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_58188,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != k1_xboole_0
    | k1_xboole_0 = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_58187])).

cnf(c_115581,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5073,c_30,c_27,c_70,c_1264,c_2198,c_2258,c_2315,c_2345,c_2346,c_2477,c_2478,c_2514,c_2515,c_2598,c_2823,c_2880,c_3253,c_3255,c_3370,c_3431,c_23822,c_28851,c_28853,c_53136,c_58188])).

cnf(c_4643,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_funct_1(sK6,sK2(sK6,sK5)),k2_relat_1(sK6))
    | X0 != k1_funct_1(sK6,sK2(sK6,sK5))
    | X1 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_25935,plain,
    ( r2_hidden(sK1(sK6,sK5),X0)
    | ~ r2_hidden(k1_funct_1(sK6,sK2(sK6,sK5)),k2_relat_1(sK6))
    | X0 != k2_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_4643])).

cnf(c_109177,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | ~ r2_hidden(k1_funct_1(sK6,sK2(sK6,sK5)),k2_relat_1(sK6))
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5))
    | k2_relat_1(sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_25935])).

cnf(c_4206,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | X0 != sK7(sK1(sK6,sK5))
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_11740,plain,
    ( r2_hidden(sK7(sK1(sK6,sK5)),X0)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | X0 != sK4
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_4206])).

cnf(c_81980,plain,
    ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
    | k1_relat_1(sK6) != sK4 ),
    inference(instantiation,[status(thm)],[c_11740])).

cnf(c_12115,plain,
    ( X0 != X1
    | X0 = sK1(sK6,X2)
    | sK1(sK6,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_29723,plain,
    ( X0 = sK1(sK6,sK5)
    | X0 != k1_funct_1(sK6,sK2(sK6,sK5))
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_12115])).

cnf(c_29724,plain,
    ( sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5))
    | k1_xboole_0 = sK1(sK6,sK5)
    | k1_xboole_0 != k1_funct_1(sK6,sK2(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_29723])).

cnf(c_25928,plain,
    ( ~ r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5))
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_19903,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_8976,plain,
    ( sK1(sK6,X0) != sK1(sK6,X0)
    | sK1(sK6,X0) = k1_funct_1(sK6,sK2(sK6,X0))
    | k1_funct_1(sK6,sK2(sK6,X0)) != sK1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_4493])).

cnf(c_12096,plain,
    ( sK1(sK6,sK5) != sK1(sK6,sK5)
    | sK1(sK6,sK5) = k1_funct_1(sK6,sK2(sK6,sK5))
    | k1_funct_1(sK6,sK2(sK6,sK5)) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_8976])).

cnf(c_11741,plain,
    ( sK7(sK1(sK6,sK5)) = sK7(sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_8748,plain,
    ( X0 != X1
    | X0 = k1_funct_1(sK6,sK2(sK6,sK5))
    | k1_funct_1(sK6,sK2(sK6,sK5)) != X1 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_8749,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) != k1_xboole_0
    | k1_xboole_0 = k1_funct_1(sK6,sK2(sK6,sK5))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8748])).

cnf(c_1878,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2938,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1875,c_1878])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1880,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3508,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2938,c_1880])).

cnf(c_35,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4030,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3508,c_35])).

cnf(c_4035,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4030,c_1883])).

cnf(c_4036,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4035])).

cnf(c_3741,plain,
    ( k2_relat_1(sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_3368,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3355,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK6,sK5),sK5)
    | X0 != sK1(sK6,sK5)
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_3365,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK1(sK6,sK5)
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3355])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_656,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_657,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_3273,plain,
    ( ~ r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,sK2(sK6,sK5)),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_590,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_591,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_2597,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_119491,c_115581,c_109177,c_81980,c_29724,c_25928,c_25868,c_19903,c_12096,c_11741,c_11395,c_8980,c_8749,c_4036,c_3741,c_3368,c_3369,c_3365,c_3273,c_3184,c_2880,c_2823,c_2598,c_2597,c_2514,c_2477,c_2346,c_2315,c_2258,c_2198,c_1264,c_70,c_27,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.59/4.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.59/4.50  
% 31.59/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.59/4.50  
% 31.59/4.50  ------  iProver source info
% 31.59/4.50  
% 31.59/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.59/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.59/4.50  git: non_committed_changes: false
% 31.59/4.50  git: last_make_outside_of_git: false
% 31.59/4.50  
% 31.59/4.50  ------ 
% 31.59/4.50  ------ Parsing...
% 31.59/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.59/4.50  
% 31.59/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 31.59/4.50  
% 31.59/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.59/4.50  
% 31.59/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.59/4.50  ------ Proving...
% 31.59/4.50  ------ Problem Properties 
% 31.59/4.50  
% 31.59/4.50  
% 31.59/4.50  clauses                                 27
% 31.59/4.50  conjectures                             4
% 31.59/4.50  EPR                                     3
% 31.59/4.50  Horn                                    21
% 31.59/4.50  unary                                   3
% 31.59/4.50  binary                                  11
% 31.59/4.50  lits                                    70
% 31.59/4.50  lits eq                                 19
% 31.59/4.50  fd_pure                                 0
% 31.59/4.50  fd_pseudo                               0
% 31.59/4.50  fd_cond                                 3
% 31.59/4.50  fd_pseudo_cond                          1
% 31.59/4.50  AC symbols                              0
% 31.59/4.50  
% 31.59/4.50  ------ Input Options Time Limit: Unbounded
% 31.59/4.50  
% 31.59/4.50  
% 31.59/4.50  ------ 
% 31.59/4.50  Current options:
% 31.59/4.50  ------ 
% 31.59/4.50  
% 31.59/4.50  
% 31.59/4.50  
% 31.59/4.50  
% 31.59/4.50  ------ Proving...
% 31.59/4.50  
% 31.59/4.50  
% 31.59/4.50  % SZS status Theorem for theBenchmark.p
% 31.59/4.50  
% 31.59/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.59/4.50  
% 31.59/4.50  fof(f1,axiom,(
% 31.59/4.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f14,plain,(
% 31.59/4.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 31.59/4.50    inference(ennf_transformation,[],[f1])).
% 31.59/4.50  
% 31.59/4.50  fof(f28,plain,(
% 31.59/4.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 31.59/4.50    inference(nnf_transformation,[],[f14])).
% 31.59/4.50  
% 31.59/4.50  fof(f29,plain,(
% 31.59/4.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.59/4.50    inference(rectify,[],[f28])).
% 31.59/4.50  
% 31.59/4.50  fof(f30,plain,(
% 31.59/4.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 31.59/4.50    introduced(choice_axiom,[])).
% 31.59/4.50  
% 31.59/4.50  fof(f31,plain,(
% 31.59/4.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.59/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 31.59/4.50  
% 31.59/4.50  fof(f44,plain,(
% 31.59/4.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f31])).
% 31.59/4.50  
% 31.59/4.50  fof(f6,axiom,(
% 31.59/4.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f18,plain,(
% 31.59/4.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.59/4.50    inference(ennf_transformation,[],[f6])).
% 31.59/4.50  
% 31.59/4.50  fof(f19,plain,(
% 31.59/4.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.59/4.50    inference(flattening,[],[f18])).
% 31.59/4.50  
% 31.59/4.50  fof(f34,plain,(
% 31.59/4.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.59/4.50    inference(nnf_transformation,[],[f19])).
% 31.59/4.50  
% 31.59/4.50  fof(f35,plain,(
% 31.59/4.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.59/4.50    inference(rectify,[],[f34])).
% 31.59/4.50  
% 31.59/4.50  fof(f38,plain,(
% 31.59/4.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 31.59/4.50    introduced(choice_axiom,[])).
% 31.59/4.50  
% 31.59/4.50  fof(f37,plain,(
% 31.59/4.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 31.59/4.50    introduced(choice_axiom,[])).
% 31.59/4.50  
% 31.59/4.50  fof(f36,plain,(
% 31.59/4.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 31.59/4.50    introduced(choice_axiom,[])).
% 31.59/4.50  
% 31.59/4.50  fof(f39,plain,(
% 31.59/4.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.59/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 31.59/4.50  
% 31.59/4.50  fof(f59,plain,(
% 31.59/4.50    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f39])).
% 31.59/4.50  
% 31.59/4.50  fof(f12,conjecture,(
% 31.59/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f13,negated_conjecture,(
% 31.59/4.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 31.59/4.50    inference(negated_conjecture,[],[f12])).
% 31.59/4.50  
% 31.59/4.50  fof(f26,plain,(
% 31.59/4.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 31.59/4.50    inference(ennf_transformation,[],[f13])).
% 31.59/4.50  
% 31.59/4.50  fof(f27,plain,(
% 31.59/4.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 31.59/4.50    inference(flattening,[],[f26])).
% 31.59/4.50  
% 31.59/4.50  fof(f42,plain,(
% 31.59/4.50    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 31.59/4.50    introduced(choice_axiom,[])).
% 31.59/4.50  
% 31.59/4.50  fof(f41,plain,(
% 31.59/4.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 31.59/4.50    introduced(choice_axiom,[])).
% 31.59/4.50  
% 31.59/4.50  fof(f43,plain,(
% 31.59/4.50    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 31.59/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f42,f41])).
% 31.59/4.50  
% 31.59/4.50  fof(f71,plain,(
% 31.59/4.50    v1_funct_1(sK6)),
% 31.59/4.50    inference(cnf_transformation,[],[f43])).
% 31.59/4.50  
% 31.59/4.50  fof(f73,plain,(
% 31.59/4.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 31.59/4.50    inference(cnf_transformation,[],[f43])).
% 31.59/4.50  
% 31.59/4.50  fof(f2,axiom,(
% 31.59/4.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f32,plain,(
% 31.59/4.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.59/4.50    inference(nnf_transformation,[],[f2])).
% 31.59/4.50  
% 31.59/4.50  fof(f47,plain,(
% 31.59/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.59/4.50    inference(cnf_transformation,[],[f32])).
% 31.59/4.50  
% 31.59/4.50  fof(f3,axiom,(
% 31.59/4.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f15,plain,(
% 31.59/4.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.59/4.50    inference(ennf_transformation,[],[f3])).
% 31.59/4.50  
% 31.59/4.50  fof(f49,plain,(
% 31.59/4.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f15])).
% 31.59/4.50  
% 31.59/4.50  fof(f48,plain,(
% 31.59/4.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f32])).
% 31.59/4.50  
% 31.59/4.50  fof(f4,axiom,(
% 31.59/4.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f50,plain,(
% 31.59/4.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.59/4.50    inference(cnf_transformation,[],[f4])).
% 31.59/4.50  
% 31.59/4.50  fof(f75,plain,(
% 31.59/4.50    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f43])).
% 31.59/4.50  
% 31.59/4.50  fof(f76,plain,(
% 31.59/4.50    k2_relset_1(sK4,sK5,sK6) != sK5),
% 31.59/4.50    inference(cnf_transformation,[],[f43])).
% 31.59/4.50  
% 31.59/4.50  fof(f10,axiom,(
% 31.59/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f23,plain,(
% 31.59/4.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.59/4.50    inference(ennf_transformation,[],[f10])).
% 31.59/4.50  
% 31.59/4.50  fof(f64,plain,(
% 31.59/4.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.59/4.50    inference(cnf_transformation,[],[f23])).
% 31.59/4.50  
% 31.59/4.50  fof(f5,axiom,(
% 31.59/4.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f16,plain,(
% 31.59/4.50    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.59/4.50    inference(ennf_transformation,[],[f5])).
% 31.59/4.50  
% 31.59/4.50  fof(f17,plain,(
% 31.59/4.50    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.59/4.50    inference(flattening,[],[f16])).
% 31.59/4.50  
% 31.59/4.50  fof(f33,plain,(
% 31.59/4.50    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.59/4.50    inference(nnf_transformation,[],[f17])).
% 31.59/4.50  
% 31.59/4.50  fof(f51,plain,(
% 31.59/4.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f33])).
% 31.59/4.50  
% 31.59/4.50  fof(f79,plain,(
% 31.59/4.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(equality_resolution,[],[f51])).
% 31.59/4.50  
% 31.59/4.50  fof(f7,axiom,(
% 31.59/4.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f20,plain,(
% 31.59/4.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 31.59/4.50    inference(ennf_transformation,[],[f7])).
% 31.59/4.50  
% 31.59/4.50  fof(f61,plain,(
% 31.59/4.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f20])).
% 31.59/4.50  
% 31.59/4.50  fof(f45,plain,(
% 31.59/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f31])).
% 31.59/4.50  
% 31.59/4.50  fof(f46,plain,(
% 31.59/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f31])).
% 31.59/4.50  
% 31.59/4.50  fof(f74,plain,(
% 31.59/4.50    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f43])).
% 31.59/4.50  
% 31.59/4.50  fof(f54,plain,(
% 31.59/4.50    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f33])).
% 31.59/4.50  
% 31.59/4.50  fof(f77,plain,(
% 31.59/4.50    ( ! [X0,X1] : (k1_funct_1(X0,X1) = k1_xboole_0 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(equality_resolution,[],[f54])).
% 31.59/4.50  
% 31.59/4.50  fof(f60,plain,(
% 31.59/4.50    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f39])).
% 31.59/4.50  
% 31.59/4.50  fof(f11,axiom,(
% 31.59/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f24,plain,(
% 31.59/4.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.59/4.50    inference(ennf_transformation,[],[f11])).
% 31.59/4.50  
% 31.59/4.50  fof(f25,plain,(
% 31.59/4.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.59/4.50    inference(flattening,[],[f24])).
% 31.59/4.50  
% 31.59/4.50  fof(f40,plain,(
% 31.59/4.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.59/4.50    inference(nnf_transformation,[],[f25])).
% 31.59/4.50  
% 31.59/4.50  fof(f65,plain,(
% 31.59/4.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.59/4.50    inference(cnf_transformation,[],[f40])).
% 31.59/4.50  
% 31.59/4.50  fof(f72,plain,(
% 31.59/4.50    v1_funct_2(sK6,sK4,sK5)),
% 31.59/4.50    inference(cnf_transformation,[],[f43])).
% 31.59/4.50  
% 31.59/4.50  fof(f9,axiom,(
% 31.59/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f22,plain,(
% 31.59/4.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.59/4.50    inference(ennf_transformation,[],[f9])).
% 31.59/4.50  
% 31.59/4.50  fof(f63,plain,(
% 31.59/4.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.59/4.50    inference(cnf_transformation,[],[f22])).
% 31.59/4.50  
% 31.59/4.50  fof(f8,axiom,(
% 31.59/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 31.59/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.59/4.50  
% 31.59/4.50  fof(f21,plain,(
% 31.59/4.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.59/4.50    inference(ennf_transformation,[],[f8])).
% 31.59/4.50  
% 31.59/4.50  fof(f62,plain,(
% 31.59/4.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.59/4.50    inference(cnf_transformation,[],[f21])).
% 31.59/4.50  
% 31.59/4.50  fof(f57,plain,(
% 31.59/4.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f39])).
% 31.59/4.50  
% 31.59/4.50  fof(f80,plain,(
% 31.59/4.50    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(equality_resolution,[],[f57])).
% 31.59/4.50  
% 31.59/4.50  fof(f81,plain,(
% 31.59/4.50    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(equality_resolution,[],[f80])).
% 31.59/4.50  
% 31.59/4.50  fof(f58,plain,(
% 31.59/4.50    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.59/4.50    inference(cnf_transformation,[],[f39])).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2,plain,
% 31.59/4.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 31.59/4.50      inference(cnf_transformation,[],[f44]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_12025,plain,
% 31.59/4.50      ( ~ r2_hidden(sK1(sK6,X0),X1)
% 31.59/4.50      | r2_hidden(sK1(sK6,X0),X2)
% 31.59/4.50      | ~ r1_tarski(X1,X2) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_2]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_29470,plain,
% 31.59/4.50      ( ~ r2_hidden(sK1(sK6,sK5),X0)
% 31.59/4.50      | r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.50      | ~ r1_tarski(X0,sK5) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_12025]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_119491,plain,
% 31.59/4.50      ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 31.59/4.50      | r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.50      | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_29470]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_12,plain,
% 31.59/4.50      ( r2_hidden(sK1(X0,X1),X1)
% 31.59/4.50      | ~ v1_funct_1(X0)
% 31.59/4.50      | ~ v1_relat_1(X0)
% 31.59/4.50      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 31.59/4.50      | k2_relat_1(X0) = X1 ),
% 31.59/4.50      inference(cnf_transformation,[],[f59]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_32,negated_conjecture,
% 31.59/4.50      ( v1_funct_1(sK6) ),
% 31.59/4.50      inference(cnf_transformation,[],[f71]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_608,plain,
% 31.59/4.50      ( r2_hidden(sK1(X0,X1),X1)
% 31.59/4.50      | ~ v1_relat_1(X0)
% 31.59/4.50      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 31.59/4.50      | k2_relat_1(X0) = X1
% 31.59/4.50      | sK6 != X0 ),
% 31.59/4.50      inference(resolution_lifted,[status(thm)],[c_12,c_32]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_609,plain,
% 31.59/4.50      ( r2_hidden(sK1(sK6,X0),X0)
% 31.59/4.50      | ~ v1_relat_1(sK6)
% 31.59/4.50      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 31.59/4.50      | k2_relat_1(sK6) = X0 ),
% 31.59/4.50      inference(unflattening,[status(thm)],[c_608]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1872,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 31.59/4.50      | k2_relat_1(sK6) = X0
% 31.59/4.50      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_610,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 31.59/4.50      | k2_relat_1(sK6) = X0
% 31.59/4.50      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_30,negated_conjecture,
% 31.59/4.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 31.59/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1875,plain,
% 31.59/4.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_4,plain,
% 31.59/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.59/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1883,plain,
% 31.59/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.59/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2345,plain,
% 31.59/4.50      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_1875,c_1883]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_5,plain,
% 31.59/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.59/4.50      | ~ v1_relat_1(X1)
% 31.59/4.50      | v1_relat_1(X0) ),
% 31.59/4.50      inference(cnf_transformation,[],[f49]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3,plain,
% 31.59/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.59/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_256,plain,
% 31.59/4.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.59/4.50      inference(prop_impl,[status(thm)],[c_3]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_257,plain,
% 31.59/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.59/4.50      inference(renaming,[status(thm)],[c_256]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_320,plain,
% 31.59/4.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.59/4.50      inference(bin_hyper_res,[status(thm)],[c_5,c_257]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2249,plain,
% 31.59/4.50      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 31.59/4.50      | v1_relat_1(X0)
% 31.59/4.50      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_320]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2377,plain,
% 31.59/4.50      ( ~ r1_tarski(sK6,k2_zfmisc_1(X0,X1))
% 31.59/4.50      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 31.59/4.50      | v1_relat_1(sK6) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_2249]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2477,plain,
% 31.59/4.50      ( ~ r1_tarski(sK6,k2_zfmisc_1(sK4,sK5))
% 31.59/4.50      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 31.59/4.50      | v1_relat_1(sK6) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_2377]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2478,plain,
% 31.59/4.50      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) != iProver_top
% 31.59/4.50      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 31.59/4.50      | v1_relat_1(sK6) = iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_2477]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_6,plain,
% 31.59/4.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.59/4.50      inference(cnf_transformation,[],[f50]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2514,plain,
% 31.59/4.50      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_6]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2515,plain,
% 31.59/4.50      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_2514]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2764,plain,
% 31.59/4.50      ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 31.59/4.50      | k2_relat_1(sK6) = X0
% 31.59/4.50      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
% 31.59/4.50      inference(global_propositional_subsumption,
% 31.59/4.50                [status(thm)],
% 31.59/4.50                [c_1872,c_610,c_2345,c_2478,c_2515]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2765,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 31.59/4.50      | k2_relat_1(sK6) = X0
% 31.59/4.50      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 31.59/4.50      inference(renaming,[status(thm)],[c_2764]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_28,negated_conjecture,
% 31.59/4.50      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 31.59/4.50      inference(cnf_transformation,[],[f75]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1877,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2774,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 31.59/4.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 31.59/4.50      | k2_relat_1(sK6) = sK5 ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_2765,c_1877]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_27,negated_conjecture,
% 31.59/4.50      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 31.59/4.50      inference(cnf_transformation,[],[f76]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_20,plain,
% 31.59/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.59/4.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.59/4.50      inference(cnf_transformation,[],[f64]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2198,plain,
% 31.59/4.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 31.59/4.50      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_20]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1233,plain,( X0 = X0 ),theory(equality) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2258,plain,
% 31.59/4.50      ( sK5 = sK5 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_1233]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1234,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2256,plain,
% 31.59/4.50      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_1234]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2316,plain,
% 31.59/4.50      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_2256]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2598,plain,
% 31.59/4.50      ( k2_relat_1(sK6) != sK5 | sK5 = k2_relat_1(sK6) | sK5 != sK5 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_2316]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2149,plain,
% 31.59/4.50      ( k2_relset_1(sK4,sK5,sK6) != X0
% 31.59/4.50      | k2_relset_1(sK4,sK5,sK6) = sK5
% 31.59/4.50      | sK5 != X0 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_1234]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2823,plain,
% 31.59/4.50      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 31.59/4.50      | k2_relset_1(sK4,sK5,sK6) = sK5
% 31.59/4.50      | sK5 != k2_relat_1(sK6) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_2149]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3430,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 31.59/4.50      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 31.59/4.50      inference(global_propositional_subsumption,
% 31.59/4.50                [status(thm)],
% 31.59/4.50                [c_2774,c_30,c_27,c_2198,c_2258,c_2598,c_2823]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3431,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 31.59/4.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 31.59/4.50      inference(renaming,[status(thm)],[c_3430]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_10,plain,
% 31.59/4.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 31.59/4.50      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 31.59/4.50      | ~ v1_funct_1(X1)
% 31.59/4.50      | ~ v1_relat_1(X1) ),
% 31.59/4.50      inference(cnf_transformation,[],[f79]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_692,plain,
% 31.59/4.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 31.59/4.50      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 31.59/4.50      | ~ v1_relat_1(X1)
% 31.59/4.50      | sK6 != X1 ),
% 31.59/4.50      inference(resolution_lifted,[status(thm)],[c_10,c_32]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_693,plain,
% 31.59/4.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 31.59/4.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 31.59/4.50      | ~ v1_relat_1(sK6) ),
% 31.59/4.50      inference(unflattening,[status(thm)],[c_692]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1867,plain,
% 31.59/4.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_694,plain,
% 31.59/4.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2519,plain,
% 31.59/4.50      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 31.59/4.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 31.59/4.50      inference(global_propositional_subsumption,
% 31.59/4.50                [status(thm)],
% 31.59/4.50                [c_1867,c_694,c_2345,c_2478,c_2515]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2520,plain,
% 31.59/4.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
% 31.59/4.50      inference(renaming,[status(thm)],[c_2519]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1885,plain,
% 31.59/4.50      ( r2_hidden(X0,X1) != iProver_top
% 31.59/4.50      | r2_hidden(X0,X2) = iProver_top
% 31.59/4.50      | r1_tarski(X1,X2) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3550,plain,
% 31.59/4.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),X1) = iProver_top
% 31.59/4.50      | r1_tarski(sK6,X1) != iProver_top ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_2520,c_1885]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_5073,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 31.59/4.50      | r2_hidden(k4_tarski(sK7(sK1(sK6,sK5)),sK1(sK6,sK5)),X0) = iProver_top
% 31.59/4.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | r1_tarski(sK6,X0) != iProver_top ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_3431,c_3550]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_17,plain,
% 31.59/4.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 31.59/4.50      inference(cnf_transformation,[],[f61]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_70,plain,
% 31.59/4.50      ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 31.59/4.50      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_17]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1264,plain,
% 31.59/4.50      ( k1_xboole_0 = k1_xboole_0 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_1233]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2314,plain,
% 31.59/4.50      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_1234]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2315,plain,
% 31.59/4.50      ( sK5 != k1_xboole_0
% 31.59/4.50      | k1_xboole_0 = sK5
% 31.59/4.50      | k1_xboole_0 != k1_xboole_0 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_2314]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2346,plain,
% 31.59/4.50      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) ),
% 31.59/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_2345]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1,plain,
% 31.59/4.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 31.59/4.50      inference(cnf_transformation,[],[f45]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1886,plain,
% 31.59/4.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 31.59/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_0,plain,
% 31.59/4.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 31.59/4.50      inference(cnf_transformation,[],[f46]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1887,plain,
% 31.59/4.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 31.59/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2870,plain,
% 31.59/4.50      ( r1_tarski(X0,X0) = iProver_top ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_1886,c_1887]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2878,plain,
% 31.59/4.50      ( r1_tarski(X0,X0) ),
% 31.59/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_2870]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2880,plain,
% 31.59/4.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_2878]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3253,plain,
% 31.59/4.50      ( r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.50      | ~ v1_relat_1(sK6)
% 31.59/4.50      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 31.59/4.50      | k2_relat_1(sK6) = sK5 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_609]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3255,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 31.59/4.50      | k2_relat_1(sK6) = sK5
% 31.59/4.50      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_3253]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_29,negated_conjecture,
% 31.59/4.50      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 31.59/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3369,plain,
% 31.59/4.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_29]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3370,plain,
% 31.59/4.50      ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 31.59/4.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_3369]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1235,plain,
% 31.59/4.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.59/4.50      theory(equality) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3689,plain,
% 31.59/4.50      ( r2_hidden(X0,X1)
% 31.59/4.50      | ~ r2_hidden(sK1(sK6,X2),X2)
% 31.59/4.50      | X1 != X2
% 31.59/4.50      | X0 != sK1(sK6,X2) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_1235]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_12130,plain,
% 31.59/4.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.50      | r2_hidden(k1_funct_1(sK6,sK7(sK1(sK6,sK5))),X0)
% 31.59/4.50      | X0 != sK5
% 31.59/4.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_3689]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_23822,plain,
% 31.59/4.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.50      | r2_hidden(k1_funct_1(sK6,sK7(sK1(sK6,sK5))),sK5)
% 31.59/4.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5)
% 31.59/4.50      | sK5 != sK5 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_12130]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_7,plain,
% 31.59/4.50      ( r2_hidden(X0,k1_relat_1(X1))
% 31.59/4.50      | ~ v1_funct_1(X1)
% 31.59/4.50      | ~ v1_relat_1(X1)
% 31.59/4.50      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 31.59/4.50      inference(cnf_transformation,[],[f77]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_725,plain,
% 31.59/4.50      ( r2_hidden(X0,k1_relat_1(X1))
% 31.59/4.50      | ~ v1_relat_1(X1)
% 31.59/4.50      | k1_funct_1(X1,X0) = k1_xboole_0
% 31.59/4.50      | sK6 != X1 ),
% 31.59/4.50      inference(resolution_lifted,[status(thm)],[c_7,c_32]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_726,plain,
% 31.59/4.50      ( r2_hidden(X0,k1_relat_1(sK6))
% 31.59/4.50      | ~ v1_relat_1(sK6)
% 31.59/4.50      | k1_funct_1(sK6,X0) = k1_xboole_0 ),
% 31.59/4.50      inference(unflattening,[status(thm)],[c_725]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1865,plain,
% 31.59/4.50      ( k1_funct_1(sK6,X0) = k1_xboole_0
% 31.59/4.50      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_727,plain,
% 31.59/4.50      ( k1_funct_1(sK6,X0) = k1_xboole_0
% 31.59/4.50      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2630,plain,
% 31.59/4.50      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 31.59/4.50      | k1_funct_1(sK6,X0) = k1_xboole_0 ),
% 31.59/4.50      inference(global_propositional_subsumption,
% 31.59/4.50                [status(thm)],
% 31.59/4.50                [c_1865,c_727,c_2345,c_2478,c_2515]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2631,plain,
% 31.59/4.50      ( k1_funct_1(sK6,X0) = k1_xboole_0
% 31.59/4.50      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 31.59/4.50      inference(renaming,[status(thm)],[c_2630]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_11,plain,
% 31.59/4.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 31.59/4.50      | ~ r2_hidden(sK1(X1,X2),X2)
% 31.59/4.50      | ~ v1_funct_1(X1)
% 31.59/4.50      | ~ v1_relat_1(X1)
% 31.59/4.50      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 31.59/4.50      | k2_relat_1(X1) = X2 ),
% 31.59/4.50      inference(cnf_transformation,[],[f60]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_671,plain,
% 31.59/4.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 31.59/4.50      | ~ r2_hidden(sK1(X1,X2),X2)
% 31.59/4.50      | ~ v1_relat_1(X1)
% 31.59/4.50      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 31.59/4.50      | k2_relat_1(X1) = X2
% 31.59/4.50      | sK6 != X1 ),
% 31.59/4.50      inference(resolution_lifted,[status(thm)],[c_11,c_32]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_672,plain,
% 31.59/4.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 31.59/4.50      | ~ r2_hidden(sK1(sK6,X1),X1)
% 31.59/4.50      | ~ v1_relat_1(sK6)
% 31.59/4.50      | sK1(sK6,X1) != k1_funct_1(sK6,X0)
% 31.59/4.50      | k2_relat_1(sK6) = X1 ),
% 31.59/4.50      inference(unflattening,[status(thm)],[c_671]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1868,plain,
% 31.59/4.50      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 31.59/4.50      | k2_relat_1(sK6) = X0
% 31.59/4.50      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_673,plain,
% 31.59/4.50      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 31.59/4.50      | k2_relat_1(sK6) = X0
% 31.59/4.50      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2619,plain,
% 31.59/4.50      ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 31.59/4.50      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | k2_relat_1(sK6) = X0
% 31.59/4.50      | sK1(sK6,X0) != k1_funct_1(sK6,X1) ),
% 31.59/4.50      inference(global_propositional_subsumption,
% 31.59/4.50                [status(thm)],
% 31.59/4.50                [c_1868,c_673,c_2345,c_2478,c_2515]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2620,plain,
% 31.59/4.50      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 31.59/4.50      | k2_relat_1(sK6) = X0
% 31.59/4.50      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
% 31.59/4.50      inference(renaming,[status(thm)],[c_2619]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3436,plain,
% 31.59/4.50      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 31.59/4.50      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 31.59/4.50      | k2_relat_1(sK6) = X0
% 31.59/4.50      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 31.59/4.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_3431,c_2620]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3374,plain,
% 31.59/4.50      ( sK1(sK6,X0) != X1
% 31.59/4.50      | sK1(sK6,X0) = k1_funct_1(sK6,X2)
% 31.59/4.50      | k1_funct_1(sK6,X2) != X1 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_1234]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_4493,plain,
% 31.59/4.50      ( sK1(sK6,X0) != sK1(sK6,X0)
% 31.59/4.50      | sK1(sK6,X0) = k1_funct_1(sK6,X1)
% 31.59/4.50      | k1_funct_1(sK6,X1) != sK1(sK6,X0) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_3374]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_8980,plain,
% 31.59/4.50      ( sK1(sK6,sK5) != sK1(sK6,sK5)
% 31.59/4.50      | sK1(sK6,sK5) = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 31.59/4.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_4493]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_4494,plain,
% 31.59/4.50      ( sK1(sK6,X0) = sK1(sK6,X0) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_1233]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_11395,plain,
% 31.59/4.50      ( sK1(sK6,sK5) = sK1(sK6,sK5) ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_4494]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_25868,plain,
% 31.59/4.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.50      | ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
% 31.59/4.50      | ~ v1_relat_1(sK6)
% 31.59/4.50      | sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 31.59/4.50      | k2_relat_1(sK6) = sK5 ),
% 31.59/4.50      inference(instantiation,[status(thm)],[c_672]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_25869,plain,
% 31.59/4.50      ( sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 31.59/4.50      | k2_relat_1(sK6) = sK5
% 31.59/4.50      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 31.59/4.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 31.59/4.50      | v1_relat_1(sK6) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_25868]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_28845,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 31.59/4.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 31.59/4.50      inference(global_propositional_subsumption,
% 31.59/4.50                [status(thm)],
% 31.59/4.50                [c_3436,c_30,c_27,c_2198,c_2258,c_2345,c_2478,c_2515,
% 31.59/4.50                 c_2598,c_2823,c_3255,c_3431,c_8980,c_11395,c_25869]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_28851,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 31.59/4.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = k1_xboole_0 ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_2631,c_28845]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_26,plain,
% 31.59/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.59/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.59/4.50      | k1_relset_1(X1,X2,X0) = X1
% 31.59/4.50      | k1_xboole_0 = X2 ),
% 31.59/4.50      inference(cnf_transformation,[],[f65]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_31,negated_conjecture,
% 31.59/4.50      ( v1_funct_2(sK6,sK4,sK5) ),
% 31.59/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_826,plain,
% 31.59/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.59/4.50      | k1_relset_1(X1,X2,X0) = X1
% 31.59/4.50      | sK6 != X0
% 31.59/4.50      | sK5 != X2
% 31.59/4.50      | sK4 != X1
% 31.59/4.50      | k1_xboole_0 = X2 ),
% 31.59/4.50      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_827,plain,
% 31.59/4.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 31.59/4.50      | k1_relset_1(sK4,sK5,sK6) = sK4
% 31.59/4.50      | k1_xboole_0 = sK5 ),
% 31.59/4.50      inference(unflattening,[status(thm)],[c_826]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_829,plain,
% 31.59/4.50      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 31.59/4.50      inference(global_propositional_subsumption,
% 31.59/4.50                [status(thm)],
% 31.59/4.50                [c_827,c_30]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_19,plain,
% 31.59/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.59/4.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 31.59/4.50      inference(cnf_transformation,[],[f63]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_1879,plain,
% 31.59/4.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.59/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.59/4.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_2952,plain,
% 31.59/4.50      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_1875,c_1879]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_3184,plain,
% 31.59/4.50      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_829,c_2952]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_28853,plain,
% 31.59/4.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 31.59/4.50      | sK5 = k1_xboole_0
% 31.59/4.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 31.59/4.50      inference(superposition,[status(thm)],[c_3184,c_28845]) ).
% 31.59/4.50  
% 31.59/4.50  cnf(c_53126,plain,
% 31.59/4.51      ( r2_hidden(X0,X1)
% 31.59/4.51      | ~ r2_hidden(k1_funct_1(sK6,sK7(sK1(sK6,sK5))),sK5)
% 31.59/4.51      | X0 != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 31.59/4.51      | X1 != sK5 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_1235]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_53136,plain,
% 31.59/4.51      ( ~ r2_hidden(k1_funct_1(sK6,sK7(sK1(sK6,sK5))),sK5)
% 31.59/4.51      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 31.59/4.51      | k1_xboole_0 != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 31.59/4.51      | k1_xboole_0 != sK5 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_53126]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_58187,plain,
% 31.59/4.51      ( X0 != X1
% 31.59/4.51      | X0 = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 31.59/4.51      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != X1 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_1234]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_58188,plain,
% 31.59/4.51      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != k1_xboole_0
% 31.59/4.51      | k1_xboole_0 = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 31.59/4.51      | k1_xboole_0 != k1_xboole_0 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_58187]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_115581,plain,
% 31.59/4.51      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 31.59/4.51      inference(global_propositional_subsumption,
% 31.59/4.51                [status(thm)],
% 31.59/4.51                [c_5073,c_30,c_27,c_70,c_1264,c_2198,c_2258,c_2315,
% 31.59/4.51                 c_2345,c_2346,c_2477,c_2478,c_2514,c_2515,c_2598,c_2823,
% 31.59/4.51                 c_2880,c_3253,c_3255,c_3370,c_3431,c_23822,c_28851,
% 31.59/4.51                 c_28853,c_53136,c_58188]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_4643,plain,
% 31.59/4.51      ( r2_hidden(X0,X1)
% 31.59/4.51      | ~ r2_hidden(k1_funct_1(sK6,sK2(sK6,sK5)),k2_relat_1(sK6))
% 31.59/4.51      | X0 != k1_funct_1(sK6,sK2(sK6,sK5))
% 31.59/4.51      | X1 != k2_relat_1(sK6) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_1235]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_25935,plain,
% 31.59/4.51      ( r2_hidden(sK1(sK6,sK5),X0)
% 31.59/4.51      | ~ r2_hidden(k1_funct_1(sK6,sK2(sK6,sK5)),k2_relat_1(sK6))
% 31.59/4.51      | X0 != k2_relat_1(sK6)
% 31.59/4.51      | sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5)) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_4643]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_109177,plain,
% 31.59/4.51      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 31.59/4.51      | ~ r2_hidden(k1_funct_1(sK6,sK2(sK6,sK5)),k2_relat_1(sK6))
% 31.59/4.51      | sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5))
% 31.59/4.51      | k2_relat_1(sK6) != k2_relat_1(sK6) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_25935]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_4206,plain,
% 31.59/4.51      ( r2_hidden(X0,X1)
% 31.59/4.51      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 31.59/4.51      | X0 != sK7(sK1(sK6,sK5))
% 31.59/4.51      | X1 != sK4 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_1235]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_11740,plain,
% 31.59/4.51      ( r2_hidden(sK7(sK1(sK6,sK5)),X0)
% 31.59/4.51      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 31.59/4.51      | X0 != sK4
% 31.59/4.51      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_4206]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_81980,plain,
% 31.59/4.51      ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
% 31.59/4.51      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 31.59/4.51      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
% 31.59/4.51      | k1_relat_1(sK6) != sK4 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_11740]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_12115,plain,
% 31.59/4.51      ( X0 != X1 | X0 = sK1(sK6,X2) | sK1(sK6,X2) != X1 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_1234]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_29723,plain,
% 31.59/4.51      ( X0 = sK1(sK6,sK5)
% 31.59/4.51      | X0 != k1_funct_1(sK6,sK2(sK6,sK5))
% 31.59/4.51      | sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5)) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_12115]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_29724,plain,
% 31.59/4.51      ( sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5))
% 31.59/4.51      | k1_xboole_0 = sK1(sK6,sK5)
% 31.59/4.51      | k1_xboole_0 != k1_funct_1(sK6,sK2(sK6,sK5)) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_29723]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_25928,plain,
% 31.59/4.51      ( ~ r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 31.59/4.51      | ~ r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.51      | ~ v1_relat_1(sK6)
% 31.59/4.51      | sK1(sK6,sK5) != k1_funct_1(sK6,sK2(sK6,sK5))
% 31.59/4.51      | k2_relat_1(sK6) = sK5 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_672]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_19903,plain,
% 31.59/4.51      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 31.59/4.51      | ~ v1_relat_1(sK6)
% 31.59/4.51      | k1_funct_1(sK6,sK2(sK6,sK5)) = k1_xboole_0 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_726]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_8976,plain,
% 31.59/4.51      ( sK1(sK6,X0) != sK1(sK6,X0)
% 31.59/4.51      | sK1(sK6,X0) = k1_funct_1(sK6,sK2(sK6,X0))
% 31.59/4.51      | k1_funct_1(sK6,sK2(sK6,X0)) != sK1(sK6,X0) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_4493]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_12096,plain,
% 31.59/4.51      ( sK1(sK6,sK5) != sK1(sK6,sK5)
% 31.59/4.51      | sK1(sK6,sK5) = k1_funct_1(sK6,sK2(sK6,sK5))
% 31.59/4.51      | k1_funct_1(sK6,sK2(sK6,sK5)) != sK1(sK6,sK5) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_8976]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_11741,plain,
% 31.59/4.51      ( sK7(sK1(sK6,sK5)) = sK7(sK1(sK6,sK5)) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_1233]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_8748,plain,
% 31.59/4.51      ( X0 != X1
% 31.59/4.51      | X0 = k1_funct_1(sK6,sK2(sK6,sK5))
% 31.59/4.51      | k1_funct_1(sK6,sK2(sK6,sK5)) != X1 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_1234]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_8749,plain,
% 31.59/4.51      ( k1_funct_1(sK6,sK2(sK6,sK5)) != k1_xboole_0
% 31.59/4.51      | k1_xboole_0 = k1_funct_1(sK6,sK2(sK6,sK5))
% 31.59/4.51      | k1_xboole_0 != k1_xboole_0 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_8748]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_1878,plain,
% 31.59/4.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 31.59/4.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.59/4.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_2938,plain,
% 31.59/4.51      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 31.59/4.51      inference(superposition,[status(thm)],[c_1875,c_1878]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_18,plain,
% 31.59/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.59/4.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 31.59/4.51      inference(cnf_transformation,[],[f62]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_1880,plain,
% 31.59/4.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.59/4.51      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 31.59/4.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_3508,plain,
% 31.59/4.51      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
% 31.59/4.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 31.59/4.51      inference(superposition,[status(thm)],[c_2938,c_1880]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_35,plain,
% 31.59/4.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 31.59/4.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_4030,plain,
% 31.59/4.51      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
% 31.59/4.51      inference(global_propositional_subsumption,
% 31.59/4.51                [status(thm)],
% 31.59/4.51                [c_3508,c_35]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_4035,plain,
% 31.59/4.51      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 31.59/4.51      inference(superposition,[status(thm)],[c_4030,c_1883]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_4036,plain,
% 31.59/4.51      ( r1_tarski(k2_relat_1(sK6),sK5) ),
% 31.59/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_4035]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_3741,plain,
% 31.59/4.51      ( k2_relat_1(sK6) = k2_relat_1(sK6) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_1233]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_3368,plain,
% 31.59/4.51      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.51      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_28]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_3355,plain,
% 31.59/4.51      ( r2_hidden(X0,X1)
% 31.59/4.51      | ~ r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.51      | X0 != sK1(sK6,sK5)
% 31.59/4.51      | X1 != sK5 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_1235]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_3365,plain,
% 31.59/4.51      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.51      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 31.59/4.51      | k1_xboole_0 != sK1(sK6,sK5)
% 31.59/4.51      | k1_xboole_0 != sK5 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_3355]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_14,plain,
% 31.59/4.51      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 31.59/4.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 31.59/4.51      | ~ v1_funct_1(X1)
% 31.59/4.51      | ~ v1_relat_1(X1) ),
% 31.59/4.51      inference(cnf_transformation,[],[f81]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_656,plain,
% 31.59/4.51      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 31.59/4.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 31.59/4.51      | ~ v1_relat_1(X1)
% 31.59/4.51      | sK6 != X1 ),
% 31.59/4.51      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_657,plain,
% 31.59/4.51      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 31.59/4.51      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 31.59/4.51      | ~ v1_relat_1(sK6) ),
% 31.59/4.51      inference(unflattening,[status(thm)],[c_656]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_3273,plain,
% 31.59/4.51      ( ~ r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 31.59/4.51      | r2_hidden(k1_funct_1(sK6,sK2(sK6,sK5)),k2_relat_1(sK6))
% 31.59/4.51      | ~ v1_relat_1(sK6) ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_657]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_13,plain,
% 31.59/4.51      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 31.59/4.51      | r2_hidden(sK1(X0,X1),X1)
% 31.59/4.51      | ~ v1_funct_1(X0)
% 31.59/4.51      | ~ v1_relat_1(X0)
% 31.59/4.51      | k2_relat_1(X0) = X1 ),
% 31.59/4.51      inference(cnf_transformation,[],[f58]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_590,plain,
% 31.59/4.51      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 31.59/4.51      | r2_hidden(sK1(X0,X1),X1)
% 31.59/4.51      | ~ v1_relat_1(X0)
% 31.59/4.51      | k2_relat_1(X0) = X1
% 31.59/4.51      | sK6 != X0 ),
% 31.59/4.51      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_591,plain,
% 31.59/4.51      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 31.59/4.51      | r2_hidden(sK1(sK6,X0),X0)
% 31.59/4.51      | ~ v1_relat_1(sK6)
% 31.59/4.51      | k2_relat_1(sK6) = X0 ),
% 31.59/4.51      inference(unflattening,[status(thm)],[c_590]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(c_2597,plain,
% 31.59/4.51      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 31.59/4.51      | r2_hidden(sK1(sK6,sK5),sK5)
% 31.59/4.51      | ~ v1_relat_1(sK6)
% 31.59/4.51      | k2_relat_1(sK6) = sK5 ),
% 31.59/4.51      inference(instantiation,[status(thm)],[c_591]) ).
% 31.59/4.51  
% 31.59/4.51  cnf(contradiction,plain,
% 31.59/4.51      ( $false ),
% 31.59/4.51      inference(minisat,
% 31.59/4.51                [status(thm)],
% 31.59/4.51                [c_119491,c_115581,c_109177,c_81980,c_29724,c_25928,
% 31.59/4.51                 c_25868,c_19903,c_12096,c_11741,c_11395,c_8980,c_8749,
% 31.59/4.51                 c_4036,c_3741,c_3368,c_3369,c_3365,c_3273,c_3184,c_2880,
% 31.59/4.51                 c_2823,c_2598,c_2597,c_2514,c_2477,c_2346,c_2315,c_2258,
% 31.59/4.51                 c_2198,c_1264,c_70,c_27,c_30]) ).
% 31.59/4.51  
% 31.59/4.51  
% 31.59/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.59/4.51  
% 31.59/4.51  ------                               Statistics
% 31.59/4.51  
% 31.59/4.51  ------ Selected
% 31.59/4.51  
% 31.59/4.51  total_time:                             3.625
% 31.59/4.51  
%------------------------------------------------------------------------------

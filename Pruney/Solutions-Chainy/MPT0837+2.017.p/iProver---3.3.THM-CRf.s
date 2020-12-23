%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:23 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 285 expanded)
%              Number of clauses        :   41 (  73 expanded)
%              Number of leaves         :   14 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  312 (1790 expanded)
%              Number of equality atoms :   69 ( 140 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
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
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f40,plain,(
    ! [X2,X3,X1] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X5,X3),X2)
          & m1_subset_1(X5,X1) )
     => ( r2_hidden(k4_tarski(sK10,X3),X2)
        & m1_subset_1(sK10,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
              ( ~ r2_hidden(k4_tarski(X4,sK9),X2)
              | ~ m1_subset_1(X4,X1) )
          | ~ r2_hidden(sK9,k2_relset_1(X1,X0,X2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,sK9),X2)
              & m1_subset_1(X5,X1) )
          | r2_hidden(sK9,k2_relset_1(X1,X0,X2)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
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
                  ( ~ r2_hidden(k4_tarski(X4,X3),sK8)
                  | ~ m1_subset_1(X4,X1) )
              | ~ r2_hidden(X3,k2_relset_1(X1,X0,sK8)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),sK8)
                  & m1_subset_1(X5,X1) )
              | r2_hidden(X3,k2_relset_1(X1,X0,sK8)) ) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
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
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                      | ~ m1_subset_1(X4,sK7) )
                  | ~ r2_hidden(X3,k2_relset_1(sK7,X0,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X5,X3),X2)
                      & m1_subset_1(X5,sK7) )
                  | r2_hidden(X3,k2_relset_1(sK7,X0,X2)) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) )
        & ~ v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
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
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,sK6,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,sK6,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK6))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK9),sK8)
          | ~ m1_subset_1(X4,sK7) )
      | ~ r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) )
    & ( ( r2_hidden(k4_tarski(sK10,sK9),sK8)
        & m1_subset_1(sK10,sK7) )
      | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))
    & ~ v1_xboole_0(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f35,f40,f39,f38,f37,f36])).

fof(f66,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK9),sK8)
      | ~ m1_subset_1(X4,sK7)
      | ~ r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK8)
    | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f67,plain,
    ( m1_subset_1(sK10,sK7)
    | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1113,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1106,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1124,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2960,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK7,sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1106,c_1124])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1129,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3429,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2960,c_1129])).

cnf(c_3571,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,X0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_3429])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1126,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4794,plain,
    ( m1_subset_1(sK5(sK8,X0),sK7) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3571,c_1126])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8888,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,X0),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4794,c_29])).

cnf(c_8889,plain,
    ( m1_subset_1(sK5(sK8,X0),sK7) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8888])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1110,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1766,plain,
    ( k2_relset_1(sK7,sK6,sK8) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1106,c_1110])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ r2_hidden(k4_tarski(X0,sK9),sK8)
    | ~ r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1109,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top
    | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1770,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top
    | r2_hidden(sK9,k2_relat_1(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1766,c_1109])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(k4_tarski(sK10,sK9),sK8)
    | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1108,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK8) = iProver_top
    | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1412,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top
    | r2_hidden(k4_tarski(sK10,sK9),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_1109])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1554,plain,
    ( ~ r2_hidden(k4_tarski(sK10,sK9),sK8)
    | r2_hidden(sK9,k2_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1555,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK8) != iProver_top
    | r2_hidden(sK9,k2_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1554])).

cnf(c_1929,plain,
    ( r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top
    | m1_subset_1(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1770,c_1412,c_1555])).

cnf(c_1930,plain,
    ( m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_1929])).

cnf(c_2020,plain,
    ( m1_subset_1(sK5(sK8,sK9),sK7) != iProver_top
    | r2_hidden(sK9,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1930])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK10,sK7)
    | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1107,plain,
    ( m1_subset_1(sK10,sK7) = iProver_top
    | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1769,plain,
    ( m1_subset_1(sK10,sK7) = iProver_top
    | r2_hidden(sK9,k2_relat_1(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1766,c_1107])).

cnf(c_1768,plain,
    ( r2_hidden(k4_tarski(sK10,sK9),sK8) = iProver_top
    | r2_hidden(sK9,k2_relat_1(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1766,c_1108])).

cnf(c_1938,plain,
    ( r2_hidden(sK9,k2_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1769,c_1555,c_1768])).

cnf(c_2048,plain,
    ( m1_subset_1(sK5(sK8,sK9),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2020,c_1555,c_1768])).

cnf(c_8898,plain,
    ( r2_hidden(sK9,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8889,c_2048])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8898,c_1938])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.40/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/0.98  
% 2.40/0.98  ------  iProver source info
% 2.40/0.98  
% 2.40/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.40/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/0.98  git: non_committed_changes: false
% 2.40/0.98  git: last_make_outside_of_git: false
% 2.40/0.98  
% 2.40/0.98  ------ 
% 2.40/0.98  
% 2.40/0.98  ------ Input Options
% 2.40/0.98  
% 2.40/0.98  --out_options                           all
% 2.40/0.98  --tptp_safe_out                         true
% 2.40/0.98  --problem_path                          ""
% 2.40/0.98  --include_path                          ""
% 2.40/0.98  --clausifier                            res/vclausify_rel
% 2.40/0.98  --clausifier_options                    --mode clausify
% 2.40/0.98  --stdin                                 false
% 2.40/0.98  --stats_out                             all
% 2.40/0.98  
% 2.40/0.98  ------ General Options
% 2.40/0.98  
% 2.40/0.98  --fof                                   false
% 2.40/0.98  --time_out_real                         305.
% 2.40/0.98  --time_out_virtual                      -1.
% 2.40/0.98  --symbol_type_check                     false
% 2.40/0.98  --clausify_out                          false
% 2.40/0.98  --sig_cnt_out                           false
% 2.40/0.98  --trig_cnt_out                          false
% 2.40/0.98  --trig_cnt_out_tolerance                1.
% 2.40/0.98  --trig_cnt_out_sk_spl                   false
% 2.40/0.98  --abstr_cl_out                          false
% 2.40/0.98  
% 2.40/0.98  ------ Global Options
% 2.40/0.98  
% 2.40/0.98  --schedule                              default
% 2.40/0.98  --add_important_lit                     false
% 2.40/0.98  --prop_solver_per_cl                    1000
% 2.40/0.98  --min_unsat_core                        false
% 2.40/0.98  --soft_assumptions                      false
% 2.40/0.98  --soft_lemma_size                       3
% 2.40/0.98  --prop_impl_unit_size                   0
% 2.40/0.98  --prop_impl_unit                        []
% 2.40/0.98  --share_sel_clauses                     true
% 2.40/0.98  --reset_solvers                         false
% 2.40/0.98  --bc_imp_inh                            [conj_cone]
% 2.40/0.98  --conj_cone_tolerance                   3.
% 2.40/0.98  --extra_neg_conj                        none
% 2.40/0.98  --large_theory_mode                     true
% 2.40/0.98  --prolific_symb_bound                   200
% 2.40/0.98  --lt_threshold                          2000
% 2.40/0.98  --clause_weak_htbl                      true
% 2.40/0.98  --gc_record_bc_elim                     false
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing Options
% 2.40/0.98  
% 2.40/0.98  --preprocessing_flag                    true
% 2.40/0.98  --time_out_prep_mult                    0.1
% 2.40/0.98  --splitting_mode                        input
% 2.40/0.98  --splitting_grd                         true
% 2.40/0.98  --splitting_cvd                         false
% 2.40/0.98  --splitting_cvd_svl                     false
% 2.40/0.98  --splitting_nvd                         32
% 2.40/0.98  --sub_typing                            true
% 2.40/0.98  --prep_gs_sim                           true
% 2.40/0.98  --prep_unflatten                        true
% 2.40/0.98  --prep_res_sim                          true
% 2.40/0.98  --prep_upred                            true
% 2.40/0.98  --prep_sem_filter                       exhaustive
% 2.40/0.98  --prep_sem_filter_out                   false
% 2.40/0.98  --pred_elim                             true
% 2.40/0.98  --res_sim_input                         true
% 2.40/0.98  --eq_ax_congr_red                       true
% 2.40/0.98  --pure_diseq_elim                       true
% 2.40/0.98  --brand_transform                       false
% 2.40/0.98  --non_eq_to_eq                          false
% 2.40/0.98  --prep_def_merge                        true
% 2.40/0.98  --prep_def_merge_prop_impl              false
% 2.40/0.98  --prep_def_merge_mbd                    true
% 2.40/0.98  --prep_def_merge_tr_red                 false
% 2.40/0.98  --prep_def_merge_tr_cl                  false
% 2.40/0.98  --smt_preprocessing                     true
% 2.40/0.98  --smt_ac_axioms                         fast
% 2.40/0.98  --preprocessed_out                      false
% 2.40/0.98  --preprocessed_stats                    false
% 2.40/0.98  
% 2.40/0.98  ------ Abstraction refinement Options
% 2.40/0.98  
% 2.40/0.98  --abstr_ref                             []
% 2.40/0.98  --abstr_ref_prep                        false
% 2.40/0.98  --abstr_ref_until_sat                   false
% 2.40/0.98  --abstr_ref_sig_restrict                funpre
% 2.40/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.98  --abstr_ref_under                       []
% 2.40/0.98  
% 2.40/0.98  ------ SAT Options
% 2.40/0.98  
% 2.40/0.98  --sat_mode                              false
% 2.40/0.98  --sat_fm_restart_options                ""
% 2.40/0.98  --sat_gr_def                            false
% 2.40/0.98  --sat_epr_types                         true
% 2.40/0.98  --sat_non_cyclic_types                  false
% 2.40/0.98  --sat_finite_models                     false
% 2.40/0.98  --sat_fm_lemmas                         false
% 2.40/0.98  --sat_fm_prep                           false
% 2.40/0.98  --sat_fm_uc_incr                        true
% 2.40/0.98  --sat_out_model                         small
% 2.40/0.98  --sat_out_clauses                       false
% 2.40/0.98  
% 2.40/0.98  ------ QBF Options
% 2.40/0.98  
% 2.40/0.98  --qbf_mode                              false
% 2.40/0.98  --qbf_elim_univ                         false
% 2.40/0.98  --qbf_dom_inst                          none
% 2.40/0.98  --qbf_dom_pre_inst                      false
% 2.40/0.98  --qbf_sk_in                             false
% 2.40/0.98  --qbf_pred_elim                         true
% 2.40/0.98  --qbf_split                             512
% 2.40/0.98  
% 2.40/0.98  ------ BMC1 Options
% 2.40/0.98  
% 2.40/0.98  --bmc1_incremental                      false
% 2.40/0.98  --bmc1_axioms                           reachable_all
% 2.40/0.98  --bmc1_min_bound                        0
% 2.40/0.98  --bmc1_max_bound                        -1
% 2.40/0.98  --bmc1_max_bound_default                -1
% 2.40/0.98  --bmc1_symbol_reachability              true
% 2.40/0.98  --bmc1_property_lemmas                  false
% 2.40/0.98  --bmc1_k_induction                      false
% 2.40/0.98  --bmc1_non_equiv_states                 false
% 2.40/0.98  --bmc1_deadlock                         false
% 2.40/0.98  --bmc1_ucm                              false
% 2.40/0.98  --bmc1_add_unsat_core                   none
% 2.40/0.98  --bmc1_unsat_core_children              false
% 2.40/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.98  --bmc1_out_stat                         full
% 2.40/0.98  --bmc1_ground_init                      false
% 2.40/0.98  --bmc1_pre_inst_next_state              false
% 2.40/0.98  --bmc1_pre_inst_state                   false
% 2.40/0.98  --bmc1_pre_inst_reach_state             false
% 2.40/0.98  --bmc1_out_unsat_core                   false
% 2.40/0.98  --bmc1_aig_witness_out                  false
% 2.40/0.98  --bmc1_verbose                          false
% 2.40/0.98  --bmc1_dump_clauses_tptp                false
% 2.40/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.98  --bmc1_dump_file                        -
% 2.40/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.98  --bmc1_ucm_extend_mode                  1
% 2.40/0.98  --bmc1_ucm_init_mode                    2
% 2.40/0.98  --bmc1_ucm_cone_mode                    none
% 2.40/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.98  --bmc1_ucm_relax_model                  4
% 2.40/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.98  --bmc1_ucm_layered_model                none
% 2.40/0.98  --bmc1_ucm_max_lemma_size               10
% 2.40/0.98  
% 2.40/0.98  ------ AIG Options
% 2.40/0.98  
% 2.40/0.98  --aig_mode                              false
% 2.40/0.98  
% 2.40/0.98  ------ Instantiation Options
% 2.40/0.98  
% 2.40/0.98  --instantiation_flag                    true
% 2.40/0.98  --inst_sos_flag                         false
% 2.40/0.98  --inst_sos_phase                        true
% 2.40/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel_side                     num_symb
% 2.40/0.98  --inst_solver_per_active                1400
% 2.40/0.98  --inst_solver_calls_frac                1.
% 2.40/0.98  --inst_passive_queue_type               priority_queues
% 2.40/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.98  --inst_passive_queues_freq              [25;2]
% 2.40/0.98  --inst_dismatching                      true
% 2.40/0.98  --inst_eager_unprocessed_to_passive     true
% 2.40/0.98  --inst_prop_sim_given                   true
% 2.40/0.98  --inst_prop_sim_new                     false
% 2.40/0.98  --inst_subs_new                         false
% 2.40/0.98  --inst_eq_res_simp                      false
% 2.40/0.98  --inst_subs_given                       false
% 2.40/0.98  --inst_orphan_elimination               true
% 2.40/0.98  --inst_learning_loop_flag               true
% 2.40/0.98  --inst_learning_start                   3000
% 2.40/0.98  --inst_learning_factor                  2
% 2.40/0.98  --inst_start_prop_sim_after_learn       3
% 2.40/0.98  --inst_sel_renew                        solver
% 2.40/0.98  --inst_lit_activity_flag                true
% 2.40/0.98  --inst_restr_to_given                   false
% 2.40/0.98  --inst_activity_threshold               500
% 2.40/0.98  --inst_out_proof                        true
% 2.40/0.98  
% 2.40/0.98  ------ Resolution Options
% 2.40/0.98  
% 2.40/0.98  --resolution_flag                       true
% 2.40/0.98  --res_lit_sel                           adaptive
% 2.40/0.98  --res_lit_sel_side                      none
% 2.40/0.98  --res_ordering                          kbo
% 2.40/0.98  --res_to_prop_solver                    active
% 2.40/0.98  --res_prop_simpl_new                    false
% 2.40/0.98  --res_prop_simpl_given                  true
% 2.40/0.98  --res_passive_queue_type                priority_queues
% 2.40/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.98  --res_passive_queues_freq               [15;5]
% 2.40/0.98  --res_forward_subs                      full
% 2.40/0.98  --res_backward_subs                     full
% 2.40/0.98  --res_forward_subs_resolution           true
% 2.40/0.98  --res_backward_subs_resolution          true
% 2.40/0.98  --res_orphan_elimination                true
% 2.40/0.98  --res_time_limit                        2.
% 2.40/0.98  --res_out_proof                         true
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Options
% 2.40/0.98  
% 2.40/0.98  --superposition_flag                    true
% 2.40/0.98  --sup_passive_queue_type                priority_queues
% 2.40/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.98  --demod_completeness_check              fast
% 2.40/0.98  --demod_use_ground                      true
% 2.40/0.98  --sup_to_prop_solver                    passive
% 2.40/0.98  --sup_prop_simpl_new                    true
% 2.40/0.98  --sup_prop_simpl_given                  true
% 2.40/0.98  --sup_fun_splitting                     false
% 2.40/0.98  --sup_smt_interval                      50000
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Simplification Setup
% 2.40/0.98  
% 2.40/0.98  --sup_indices_passive                   []
% 2.40/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_full_bw                           [BwDemod]
% 2.40/0.98  --sup_immed_triv                        [TrivRules]
% 2.40/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_immed_bw_main                     []
% 2.40/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  
% 2.40/0.98  ------ Combination Options
% 2.40/0.98  
% 2.40/0.98  --comb_res_mult                         3
% 2.40/0.98  --comb_sup_mult                         2
% 2.40/0.98  --comb_inst_mult                        10
% 2.40/0.98  
% 2.40/0.98  ------ Debug Options
% 2.40/0.98  
% 2.40/0.98  --dbg_backtrace                         false
% 2.40/0.98  --dbg_dump_prop_clauses                 false
% 2.40/0.98  --dbg_dump_prop_clauses_file            -
% 2.40/0.98  --dbg_out_stat                          false
% 2.40/0.98  ------ Parsing...
% 2.40/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.98  ------ Proving...
% 2.40/0.98  ------ Problem Properties 
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  clauses                                 28
% 2.40/0.98  conjectures                             6
% 2.40/0.98  EPR                                     6
% 2.40/0.98  Horn                                    21
% 2.40/0.98  unary                                   4
% 2.40/0.98  binary                                  8
% 2.40/0.98  lits                                    73
% 2.40/0.98  lits eq                                 7
% 2.40/0.98  fd_pure                                 0
% 2.40/0.98  fd_pseudo                               0
% 2.40/0.98  fd_cond                                 0
% 2.40/0.98  fd_pseudo_cond                          5
% 2.40/0.98  AC symbols                              0
% 2.40/0.98  
% 2.40/0.98  ------ Schedule dynamic 5 is on 
% 2.40/0.98  
% 2.40/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  ------ 
% 2.40/0.98  Current options:
% 2.40/0.98  ------ 
% 2.40/0.98  
% 2.40/0.98  ------ Input Options
% 2.40/0.98  
% 2.40/0.98  --out_options                           all
% 2.40/0.98  --tptp_safe_out                         true
% 2.40/0.98  --problem_path                          ""
% 2.40/0.98  --include_path                          ""
% 2.40/0.98  --clausifier                            res/vclausify_rel
% 2.40/0.98  --clausifier_options                    --mode clausify
% 2.40/0.98  --stdin                                 false
% 2.40/0.98  --stats_out                             all
% 2.40/0.98  
% 2.40/0.98  ------ General Options
% 2.40/0.98  
% 2.40/0.98  --fof                                   false
% 2.40/0.98  --time_out_real                         305.
% 2.40/0.98  --time_out_virtual                      -1.
% 2.40/0.98  --symbol_type_check                     false
% 2.40/0.98  --clausify_out                          false
% 2.40/0.98  --sig_cnt_out                           false
% 2.40/0.98  --trig_cnt_out                          false
% 2.40/0.98  --trig_cnt_out_tolerance                1.
% 2.40/0.98  --trig_cnt_out_sk_spl                   false
% 2.40/0.98  --abstr_cl_out                          false
% 2.40/0.98  
% 2.40/0.98  ------ Global Options
% 2.40/0.98  
% 2.40/0.98  --schedule                              default
% 2.40/0.98  --add_important_lit                     false
% 2.40/0.98  --prop_solver_per_cl                    1000
% 2.40/0.98  --min_unsat_core                        false
% 2.40/0.98  --soft_assumptions                      false
% 2.40/0.98  --soft_lemma_size                       3
% 2.40/0.98  --prop_impl_unit_size                   0
% 2.40/0.98  --prop_impl_unit                        []
% 2.40/0.98  --share_sel_clauses                     true
% 2.40/0.98  --reset_solvers                         false
% 2.40/0.98  --bc_imp_inh                            [conj_cone]
% 2.40/0.98  --conj_cone_tolerance                   3.
% 2.40/0.98  --extra_neg_conj                        none
% 2.40/0.98  --large_theory_mode                     true
% 2.40/0.98  --prolific_symb_bound                   200
% 2.40/0.98  --lt_threshold                          2000
% 2.40/0.98  --clause_weak_htbl                      true
% 2.40/0.98  --gc_record_bc_elim                     false
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing Options
% 2.40/0.98  
% 2.40/0.98  --preprocessing_flag                    true
% 2.40/0.98  --time_out_prep_mult                    0.1
% 2.40/0.98  --splitting_mode                        input
% 2.40/0.98  --splitting_grd                         true
% 2.40/0.98  --splitting_cvd                         false
% 2.40/0.98  --splitting_cvd_svl                     false
% 2.40/0.98  --splitting_nvd                         32
% 2.40/0.98  --sub_typing                            true
% 2.40/0.98  --prep_gs_sim                           true
% 2.40/0.98  --prep_unflatten                        true
% 2.40/0.98  --prep_res_sim                          true
% 2.40/0.98  --prep_upred                            true
% 2.40/0.98  --prep_sem_filter                       exhaustive
% 2.40/0.98  --prep_sem_filter_out                   false
% 2.40/0.98  --pred_elim                             true
% 2.40/0.98  --res_sim_input                         true
% 2.40/0.98  --eq_ax_congr_red                       true
% 2.40/0.98  --pure_diseq_elim                       true
% 2.40/0.98  --brand_transform                       false
% 2.40/0.98  --non_eq_to_eq                          false
% 2.40/0.98  --prep_def_merge                        true
% 2.40/0.98  --prep_def_merge_prop_impl              false
% 2.40/0.98  --prep_def_merge_mbd                    true
% 2.40/0.98  --prep_def_merge_tr_red                 false
% 2.40/0.98  --prep_def_merge_tr_cl                  false
% 2.40/0.98  --smt_preprocessing                     true
% 2.40/0.98  --smt_ac_axioms                         fast
% 2.40/0.98  --preprocessed_out                      false
% 2.40/0.98  --preprocessed_stats                    false
% 2.40/0.98  
% 2.40/0.98  ------ Abstraction refinement Options
% 2.40/0.98  
% 2.40/0.98  --abstr_ref                             []
% 2.40/0.98  --abstr_ref_prep                        false
% 2.40/0.98  --abstr_ref_until_sat                   false
% 2.40/0.98  --abstr_ref_sig_restrict                funpre
% 2.40/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.98  --abstr_ref_under                       []
% 2.40/0.98  
% 2.40/0.98  ------ SAT Options
% 2.40/0.98  
% 2.40/0.98  --sat_mode                              false
% 2.40/0.98  --sat_fm_restart_options                ""
% 2.40/0.98  --sat_gr_def                            false
% 2.40/0.98  --sat_epr_types                         true
% 2.40/0.98  --sat_non_cyclic_types                  false
% 2.40/0.98  --sat_finite_models                     false
% 2.40/0.98  --sat_fm_lemmas                         false
% 2.40/0.98  --sat_fm_prep                           false
% 2.40/0.98  --sat_fm_uc_incr                        true
% 2.40/0.98  --sat_out_model                         small
% 2.40/0.98  --sat_out_clauses                       false
% 2.40/0.98  
% 2.40/0.98  ------ QBF Options
% 2.40/0.98  
% 2.40/0.98  --qbf_mode                              false
% 2.40/0.98  --qbf_elim_univ                         false
% 2.40/0.98  --qbf_dom_inst                          none
% 2.40/0.98  --qbf_dom_pre_inst                      false
% 2.40/0.98  --qbf_sk_in                             false
% 2.40/0.98  --qbf_pred_elim                         true
% 2.40/0.98  --qbf_split                             512
% 2.40/0.98  
% 2.40/0.98  ------ BMC1 Options
% 2.40/0.98  
% 2.40/0.98  --bmc1_incremental                      false
% 2.40/0.98  --bmc1_axioms                           reachable_all
% 2.40/0.98  --bmc1_min_bound                        0
% 2.40/0.98  --bmc1_max_bound                        -1
% 2.40/0.98  --bmc1_max_bound_default                -1
% 2.40/0.98  --bmc1_symbol_reachability              true
% 2.40/0.98  --bmc1_property_lemmas                  false
% 2.40/0.98  --bmc1_k_induction                      false
% 2.40/0.98  --bmc1_non_equiv_states                 false
% 2.40/0.98  --bmc1_deadlock                         false
% 2.40/0.98  --bmc1_ucm                              false
% 2.40/0.98  --bmc1_add_unsat_core                   none
% 2.40/0.98  --bmc1_unsat_core_children              false
% 2.40/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.98  --bmc1_out_stat                         full
% 2.40/0.98  --bmc1_ground_init                      false
% 2.40/0.98  --bmc1_pre_inst_next_state              false
% 2.40/0.98  --bmc1_pre_inst_state                   false
% 2.40/0.98  --bmc1_pre_inst_reach_state             false
% 2.40/0.98  --bmc1_out_unsat_core                   false
% 2.40/0.98  --bmc1_aig_witness_out                  false
% 2.40/0.98  --bmc1_verbose                          false
% 2.40/0.98  --bmc1_dump_clauses_tptp                false
% 2.40/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.98  --bmc1_dump_file                        -
% 2.40/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.98  --bmc1_ucm_extend_mode                  1
% 2.40/0.98  --bmc1_ucm_init_mode                    2
% 2.40/0.98  --bmc1_ucm_cone_mode                    none
% 2.40/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.98  --bmc1_ucm_relax_model                  4
% 2.40/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.98  --bmc1_ucm_layered_model                none
% 2.40/0.98  --bmc1_ucm_max_lemma_size               10
% 2.40/0.98  
% 2.40/0.98  ------ AIG Options
% 2.40/0.98  
% 2.40/0.98  --aig_mode                              false
% 2.40/0.98  
% 2.40/0.98  ------ Instantiation Options
% 2.40/0.98  
% 2.40/0.98  --instantiation_flag                    true
% 2.40/0.98  --inst_sos_flag                         false
% 2.40/0.98  --inst_sos_phase                        true
% 2.40/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.98  --inst_lit_sel_side                     none
% 2.40/0.98  --inst_solver_per_active                1400
% 2.40/0.98  --inst_solver_calls_frac                1.
% 2.40/0.98  --inst_passive_queue_type               priority_queues
% 2.40/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.98  --inst_passive_queues_freq              [25;2]
% 2.40/0.98  --inst_dismatching                      true
% 2.40/0.98  --inst_eager_unprocessed_to_passive     true
% 2.40/0.98  --inst_prop_sim_given                   true
% 2.40/0.98  --inst_prop_sim_new                     false
% 2.40/0.98  --inst_subs_new                         false
% 2.40/0.98  --inst_eq_res_simp                      false
% 2.40/0.98  --inst_subs_given                       false
% 2.40/0.98  --inst_orphan_elimination               true
% 2.40/0.98  --inst_learning_loop_flag               true
% 2.40/0.98  --inst_learning_start                   3000
% 2.40/0.98  --inst_learning_factor                  2
% 2.40/0.98  --inst_start_prop_sim_after_learn       3
% 2.40/0.98  --inst_sel_renew                        solver
% 2.40/0.98  --inst_lit_activity_flag                true
% 2.40/0.98  --inst_restr_to_given                   false
% 2.40/0.98  --inst_activity_threshold               500
% 2.40/0.98  --inst_out_proof                        true
% 2.40/0.98  
% 2.40/0.98  ------ Resolution Options
% 2.40/0.98  
% 2.40/0.98  --resolution_flag                       false
% 2.40/0.98  --res_lit_sel                           adaptive
% 2.40/0.98  --res_lit_sel_side                      none
% 2.40/0.98  --res_ordering                          kbo
% 2.40/0.98  --res_to_prop_solver                    active
% 2.40/0.98  --res_prop_simpl_new                    false
% 2.40/0.98  --res_prop_simpl_given                  true
% 2.40/0.98  --res_passive_queue_type                priority_queues
% 2.40/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.98  --res_passive_queues_freq               [15;5]
% 2.40/0.98  --res_forward_subs                      full
% 2.40/0.98  --res_backward_subs                     full
% 2.40/0.98  --res_forward_subs_resolution           true
% 2.40/0.98  --res_backward_subs_resolution          true
% 2.40/0.98  --res_orphan_elimination                true
% 2.40/0.98  --res_time_limit                        2.
% 2.40/0.98  --res_out_proof                         true
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Options
% 2.40/0.98  
% 2.40/0.98  --superposition_flag                    true
% 2.40/0.98  --sup_passive_queue_type                priority_queues
% 2.40/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.98  --demod_completeness_check              fast
% 2.40/0.98  --demod_use_ground                      true
% 2.40/0.98  --sup_to_prop_solver                    passive
% 2.40/0.98  --sup_prop_simpl_new                    true
% 2.40/0.98  --sup_prop_simpl_given                  true
% 2.40/0.98  --sup_fun_splitting                     false
% 2.40/0.98  --sup_smt_interval                      50000
% 2.40/0.98  
% 2.40/0.98  ------ Superposition Simplification Setup
% 2.40/0.98  
% 2.40/0.98  --sup_indices_passive                   []
% 2.40/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_full_bw                           [BwDemod]
% 2.40/0.98  --sup_immed_triv                        [TrivRules]
% 2.40/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_immed_bw_main                     []
% 2.40/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.98  
% 2.40/0.98  ------ Combination Options
% 2.40/0.98  
% 2.40/0.98  --comb_res_mult                         3
% 2.40/0.98  --comb_sup_mult                         2
% 2.40/0.98  --comb_inst_mult                        10
% 2.40/0.98  
% 2.40/0.98  ------ Debug Options
% 2.40/0.98  
% 2.40/0.98  --dbg_backtrace                         false
% 2.40/0.98  --dbg_dump_prop_clauses                 false
% 2.40/0.98  --dbg_dump_prop_clauses_file            -
% 2.40/0.98  --dbg_out_stat                          false
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  ------ Proving...
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  % SZS status Theorem for theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  fof(f6,axiom,(
% 2.40/0.98    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f28,plain,(
% 2.40/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 2.40/0.98    inference(nnf_transformation,[],[f6])).
% 2.40/0.98  
% 2.40/0.98  fof(f29,plain,(
% 2.40/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.40/0.98    inference(rectify,[],[f28])).
% 2.40/0.98  
% 2.40/0.98  fof(f32,plain,(
% 2.40/0.98    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f31,plain,(
% 2.40/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0))) )),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f30,plain,(
% 2.40/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f33,plain,(
% 2.40/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 2.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).
% 2.40/0.98  
% 2.40/0.98  fof(f57,plain,(
% 2.40/0.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 2.40/0.98    inference(cnf_transformation,[],[f33])).
% 2.40/0.98  
% 2.40/0.98  fof(f74,plain,(
% 2.40/0.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 2.40/0.98    inference(equality_resolution,[],[f57])).
% 2.40/0.98  
% 2.40/0.98  fof(f10,conjecture,(
% 2.40/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f11,negated_conjecture,(
% 2.40/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 2.40/0.98    inference(negated_conjecture,[],[f10])).
% 2.40/0.98  
% 2.40/0.98  fof(f18,plain,(
% 2.40/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.40/0.98    inference(ennf_transformation,[],[f11])).
% 2.40/0.98  
% 2.40/0.98  fof(f34,plain,(
% 2.40/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.40/0.98    inference(nnf_transformation,[],[f18])).
% 2.40/0.98  
% 2.40/0.98  fof(f35,plain,(
% 2.40/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.40/0.98    inference(rectify,[],[f34])).
% 2.40/0.98  
% 2.40/0.98  fof(f40,plain,(
% 2.40/0.98    ( ! [X2,X3,X1] : (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) => (r2_hidden(k4_tarski(sK10,X3),X2) & m1_subset_1(sK10,X1))) )),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f39,plain,(
% 2.40/0.98    ( ! [X2,X0,X1] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK9),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(sK9,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK9),X2) & m1_subset_1(X5,X1)) | r2_hidden(sK9,k2_relset_1(X1,X0,X2))))) )),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f38,plain,(
% 2.40/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK8) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,sK8))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK8) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,sK8)))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))) )),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f37,plain,(
% 2.40/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,sK7)) | ~r2_hidden(X3,k2_relset_1(sK7,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,sK7)) | r2_hidden(X3,k2_relset_1(sK7,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK7,X0)))) & ~v1_xboole_0(sK7))) )),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f36,plain,(
% 2.40/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,sK6,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,sK6,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK6)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK6))),
% 2.40/0.98    introduced(choice_axiom,[])).
% 2.40/0.98  
% 2.40/0.98  fof(f41,plain,(
% 2.40/0.98    ((((! [X4] : (~r2_hidden(k4_tarski(X4,sK9),sK8) | ~m1_subset_1(X4,sK7)) | ~r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8))) & ((r2_hidden(k4_tarski(sK10,sK9),sK8) & m1_subset_1(sK10,sK7)) | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))) & ~v1_xboole_0(sK7)) & ~v1_xboole_0(sK6)),
% 2.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f35,f40,f39,f38,f37,f36])).
% 2.40/0.98  
% 2.40/0.98  fof(f66,plain,(
% 2.40/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6)))),
% 2.40/0.98    inference(cnf_transformation,[],[f41])).
% 2.40/0.98  
% 2.40/0.98  fof(f3,axiom,(
% 2.40/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f13,plain,(
% 2.40/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.40/0.98    inference(ennf_transformation,[],[f3])).
% 2.40/0.98  
% 2.40/0.98  fof(f49,plain,(
% 2.40/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.40/0.98    inference(cnf_transformation,[],[f13])).
% 2.40/0.98  
% 2.40/0.98  fof(f1,axiom,(
% 2.40/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f19,plain,(
% 2.40/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.40/0.98    inference(nnf_transformation,[],[f1])).
% 2.40/0.98  
% 2.40/0.98  fof(f20,plain,(
% 2.40/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.40/0.98    inference(flattening,[],[f19])).
% 2.40/0.98  
% 2.40/0.98  fof(f42,plain,(
% 2.40/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.40/0.98    inference(cnf_transformation,[],[f20])).
% 2.40/0.98  
% 2.40/0.98  fof(f2,axiom,(
% 2.40/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f12,plain,(
% 2.40/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.40/0.98    inference(ennf_transformation,[],[f2])).
% 2.40/0.98  
% 2.40/0.98  fof(f21,plain,(
% 2.40/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.40/0.98    inference(nnf_transformation,[],[f12])).
% 2.40/0.98  
% 2.40/0.98  fof(f46,plain,(
% 2.40/0.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.40/0.98    inference(cnf_transformation,[],[f21])).
% 2.40/0.98  
% 2.40/0.98  fof(f65,plain,(
% 2.40/0.98    ~v1_xboole_0(sK7)),
% 2.40/0.98    inference(cnf_transformation,[],[f41])).
% 2.40/0.98  
% 2.40/0.98  fof(f9,axiom,(
% 2.40/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.98  
% 2.40/0.98  fof(f17,plain,(
% 2.40/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.98    inference(ennf_transformation,[],[f9])).
% 2.40/0.98  
% 2.40/0.98  fof(f63,plain,(
% 2.40/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f17])).
% 2.40/0.99  
% 2.40/0.99  fof(f69,plain,(
% 2.40/0.99    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK9),sK8) | ~m1_subset_1(X4,sK7) | ~r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f41])).
% 2.40/0.99  
% 2.40/0.99  fof(f68,plain,(
% 2.40/0.99    r2_hidden(k4_tarski(sK10,sK9),sK8) | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8))),
% 2.40/0.99    inference(cnf_transformation,[],[f41])).
% 2.40/0.99  
% 2.40/0.99  fof(f58,plain,(
% 2.40/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 2.40/0.99    inference(cnf_transformation,[],[f33])).
% 2.40/0.99  
% 2.40/0.99  fof(f73,plain,(
% 2.40/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 2.40/0.99    inference(equality_resolution,[],[f58])).
% 2.40/0.99  
% 2.40/0.99  fof(f67,plain,(
% 2.40/0.99    m1_subset_1(sK10,sK7) | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8))),
% 2.40/0.99    inference(cnf_transformation,[],[f41])).
% 2.40/0.99  
% 2.40/0.99  cnf(c_18,plain,
% 2.40/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.40/0.99      | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1113,plain,
% 2.40/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 2.40/0.99      | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_25,negated_conjecture,
% 2.40/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) ),
% 2.40/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1106,plain,
% 2.40/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK7,sK6))) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_7,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.40/0.99      | ~ r2_hidden(X2,X0)
% 2.40/0.99      | r2_hidden(X2,X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1124,plain,
% 2.40/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.40/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.40/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2960,plain,
% 2.40/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK7,sK6)) = iProver_top
% 2.40/0.99      | r2_hidden(X0,sK8) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1106,c_1124]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2,plain,
% 2.40/0.99      ( r2_hidden(X0,X1)
% 2.40/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.40/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1129,plain,
% 2.40/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.40/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3429,plain,
% 2.40/0.99      ( r2_hidden(X0,sK7) = iProver_top
% 2.40/0.99      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_2960,c_1129]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_3571,plain,
% 2.40/0.99      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 2.40/0.99      | r2_hidden(sK5(sK8,X0),sK7) = iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1113,c_3429]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_5,plain,
% 2.40/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1126,plain,
% 2.40/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.40/0.99      | r2_hidden(X0,X1) != iProver_top
% 2.40/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_4794,plain,
% 2.40/0.99      ( m1_subset_1(sK5(sK8,X0),sK7) = iProver_top
% 2.40/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 2.40/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_3571,c_1126]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_26,negated_conjecture,
% 2.40/0.99      ( ~ v1_xboole_0(sK7) ),
% 2.40/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_29,plain,
% 2.40/0.99      ( v1_xboole_0(sK7) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_8888,plain,
% 2.40/0.99      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 2.40/0.99      | m1_subset_1(sK5(sK8,X0),sK7) = iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_4794,c_29]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_8889,plain,
% 2.40/0.99      ( m1_subset_1(sK5(sK8,X0),sK7) = iProver_top
% 2.40/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_8888]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_21,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1110,plain,
% 2.40/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.40/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1766,plain,
% 2.40/0.99      ( k2_relset_1(sK7,sK6,sK8) = k2_relat_1(sK8) ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1106,c_1110]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_22,negated_conjecture,
% 2.40/0.99      ( ~ m1_subset_1(X0,sK7)
% 2.40/0.99      | ~ r2_hidden(k4_tarski(X0,sK9),sK8)
% 2.40/0.99      | ~ r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) ),
% 2.40/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1109,plain,
% 2.40/0.99      ( m1_subset_1(X0,sK7) != iProver_top
% 2.40/0.99      | r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top
% 2.40/0.99      | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1770,plain,
% 2.40/0.99      ( m1_subset_1(X0,sK7) != iProver_top
% 2.40/0.99      | r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top
% 2.40/0.99      | r2_hidden(sK9,k2_relat_1(sK8)) != iProver_top ),
% 2.40/0.99      inference(demodulation,[status(thm)],[c_1766,c_1109]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_23,negated_conjecture,
% 2.40/0.99      ( r2_hidden(k4_tarski(sK10,sK9),sK8)
% 2.40/0.99      | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) ),
% 2.40/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1108,plain,
% 2.40/0.99      ( r2_hidden(k4_tarski(sK10,sK9),sK8) = iProver_top
% 2.40/0.99      | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1412,plain,
% 2.40/0.99      ( m1_subset_1(X0,sK7) != iProver_top
% 2.40/0.99      | r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top
% 2.40/0.99      | r2_hidden(k4_tarski(sK10,sK9),sK8) = iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1108,c_1109]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_17,plain,
% 2.40/0.99      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1554,plain,
% 2.40/0.99      ( ~ r2_hidden(k4_tarski(sK10,sK9),sK8)
% 2.40/0.99      | r2_hidden(sK9,k2_relat_1(sK8)) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1555,plain,
% 2.40/0.99      ( r2_hidden(k4_tarski(sK10,sK9),sK8) != iProver_top
% 2.40/0.99      | r2_hidden(sK9,k2_relat_1(sK8)) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_1554]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1929,plain,
% 2.40/0.99      ( r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top
% 2.40/0.99      | m1_subset_1(X0,sK7) != iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_1770,c_1412,c_1555]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1930,plain,
% 2.40/0.99      ( m1_subset_1(X0,sK7) != iProver_top
% 2.40/0.99      | r2_hidden(k4_tarski(X0,sK9),sK8) != iProver_top ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_1929]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2020,plain,
% 2.40/0.99      ( m1_subset_1(sK5(sK8,sK9),sK7) != iProver_top
% 2.40/0.99      | r2_hidden(sK9,k2_relat_1(sK8)) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1113,c_1930]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_24,negated_conjecture,
% 2.40/0.99      ( m1_subset_1(sK10,sK7) | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) ),
% 2.40/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1107,plain,
% 2.40/0.99      ( m1_subset_1(sK10,sK7) = iProver_top
% 2.40/0.99      | r2_hidden(sK9,k2_relset_1(sK7,sK6,sK8)) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1769,plain,
% 2.40/0.99      ( m1_subset_1(sK10,sK7) = iProver_top
% 2.40/0.99      | r2_hidden(sK9,k2_relat_1(sK8)) = iProver_top ),
% 2.40/0.99      inference(demodulation,[status(thm)],[c_1766,c_1107]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1768,plain,
% 2.40/0.99      ( r2_hidden(k4_tarski(sK10,sK9),sK8) = iProver_top
% 2.40/0.99      | r2_hidden(sK9,k2_relat_1(sK8)) = iProver_top ),
% 2.40/0.99      inference(demodulation,[status(thm)],[c_1766,c_1108]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1938,plain,
% 2.40/0.99      ( r2_hidden(sK9,k2_relat_1(sK8)) = iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_1769,c_1555,c_1768]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2048,plain,
% 2.40/0.99      ( m1_subset_1(sK5(sK8,sK9),sK7) != iProver_top ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_2020,c_1555,c_1768]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_8898,plain,
% 2.40/0.99      ( r2_hidden(sK9,k2_relat_1(sK8)) != iProver_top ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_8889,c_2048]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(contradiction,plain,
% 2.40/0.99      ( $false ),
% 2.40/0.99      inference(minisat,[status(thm)],[c_8898,c_1938]) ).
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  ------                               Statistics
% 2.40/0.99  
% 2.40/0.99  ------ General
% 2.40/0.99  
% 2.40/0.99  abstr_ref_over_cycles:                  0
% 2.40/0.99  abstr_ref_under_cycles:                 0
% 2.40/0.99  gc_basic_clause_elim:                   0
% 2.40/0.99  forced_gc_time:                         0
% 2.40/0.99  parsing_time:                           0.009
% 2.40/0.99  unif_index_cands_time:                  0.
% 2.40/0.99  unif_index_add_time:                    0.
% 2.40/0.99  orderings_time:                         0.
% 2.40/0.99  out_proof_time:                         0.008
% 2.40/0.99  total_time:                             0.266
% 2.40/0.99  num_of_symbols:                         53
% 2.40/0.99  num_of_terms:                           13125
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing
% 2.40/0.99  
% 2.40/0.99  num_of_splits:                          0
% 2.40/0.99  num_of_split_atoms:                     0
% 2.40/0.99  num_of_reused_defs:                     0
% 2.40/0.99  num_eq_ax_congr_red:                    36
% 2.40/0.99  num_of_sem_filtered_clauses:            1
% 2.40/0.99  num_of_subtypes:                        0
% 2.40/0.99  monotx_restored_types:                  0
% 2.40/0.99  sat_num_of_epr_types:                   0
% 2.40/0.99  sat_num_of_non_cyclic_types:            0
% 2.40/0.99  sat_guarded_non_collapsed_types:        0
% 2.40/0.99  num_pure_diseq_elim:                    0
% 2.40/0.99  simp_replaced_by:                       0
% 2.40/0.99  res_preprocessed:                       107
% 2.40/0.99  prep_upred:                             0
% 2.40/0.99  prep_unflattend:                        32
% 2.40/0.99  smt_new_axioms:                         0
% 2.40/0.99  pred_elim_cands:                        4
% 2.40/0.99  pred_elim:                              0
% 2.40/0.99  pred_elim_cl:                           0
% 2.40/0.99  pred_elim_cycles:                       1
% 2.40/0.99  merged_defs:                            0
% 2.40/0.99  merged_defs_ncl:                        0
% 2.40/0.99  bin_hyper_res:                          0
% 2.40/0.99  prep_cycles:                            3
% 2.40/0.99  pred_elim_time:                         0.005
% 2.40/0.99  splitting_time:                         0.
% 2.40/0.99  sem_filter_time:                        0.
% 2.40/0.99  monotx_time:                            0.
% 2.40/0.99  subtype_inf_time:                       0.
% 2.40/0.99  
% 2.40/0.99  ------ Problem properties
% 2.40/0.99  
% 2.40/0.99  clauses:                                28
% 2.40/0.99  conjectures:                            6
% 2.40/0.99  epr:                                    6
% 2.40/0.99  horn:                                   21
% 2.40/0.99  ground:                                 5
% 2.40/0.99  unary:                                  4
% 2.40/0.99  binary:                                 8
% 2.40/0.99  lits:                                   73
% 2.40/0.99  lits_eq:                                7
% 2.40/0.99  fd_pure:                                0
% 2.40/0.99  fd_pseudo:                              0
% 2.40/0.99  fd_cond:                                0
% 2.40/0.99  fd_pseudo_cond:                         5
% 2.40/0.99  ac_symbols:                             0
% 2.40/0.99  
% 2.40/0.99  ------ Propositional Solver
% 2.40/0.99  
% 2.40/0.99  prop_solver_calls:                      26
% 2.40/0.99  prop_fast_solver_calls:                 867
% 2.40/0.99  smt_solver_calls:                       0
% 2.40/0.99  smt_fast_solver_calls:                  0
% 2.40/0.99  prop_num_of_clauses:                    3973
% 2.40/0.99  prop_preprocess_simplified:             7836
% 2.40/0.99  prop_fo_subsumed:                       19
% 2.40/0.99  prop_solver_time:                       0.
% 2.40/0.99  smt_solver_time:                        0.
% 2.40/0.99  smt_fast_solver_time:                   0.
% 2.40/0.99  prop_fast_solver_time:                  0.
% 2.40/0.99  prop_unsat_core_time:                   0.
% 2.40/0.99  
% 2.40/0.99  ------ QBF
% 2.40/0.99  
% 2.40/0.99  qbf_q_res:                              0
% 2.40/0.99  qbf_num_tautologies:                    0
% 2.40/0.99  qbf_prep_cycles:                        0
% 2.40/0.99  
% 2.40/0.99  ------ BMC1
% 2.40/0.99  
% 2.40/0.99  bmc1_current_bound:                     -1
% 2.40/0.99  bmc1_last_solved_bound:                 -1
% 2.40/0.99  bmc1_unsat_core_size:                   -1
% 2.40/0.99  bmc1_unsat_core_parents_size:           -1
% 2.40/0.99  bmc1_merge_next_fun:                    0
% 2.40/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation
% 2.40/0.99  
% 2.40/0.99  inst_num_of_clauses:                    1016
% 2.40/0.99  inst_num_in_passive:                    444
% 2.40/0.99  inst_num_in_active:                     255
% 2.40/0.99  inst_num_in_unprocessed:                317
% 2.40/0.99  inst_num_of_loops:                      390
% 2.40/0.99  inst_num_of_learning_restarts:          0
% 2.40/0.99  inst_num_moves_active_passive:          132
% 2.40/0.99  inst_lit_activity:                      0
% 2.40/0.99  inst_lit_activity_moves:                1
% 2.40/0.99  inst_num_tautologies:                   0
% 2.40/0.99  inst_num_prop_implied:                  0
% 2.40/0.99  inst_num_existing_simplified:           0
% 2.40/0.99  inst_num_eq_res_simplified:             0
% 2.40/0.99  inst_num_child_elim:                    0
% 2.40/0.99  inst_num_of_dismatching_blockings:      97
% 2.40/0.99  inst_num_of_non_proper_insts:           505
% 2.40/0.99  inst_num_of_duplicates:                 0
% 2.40/0.99  inst_inst_num_from_inst_to_res:         0
% 2.40/0.99  inst_dismatching_checking_time:         0.
% 2.40/0.99  
% 2.40/0.99  ------ Resolution
% 2.40/0.99  
% 2.40/0.99  res_num_of_clauses:                     0
% 2.40/0.99  res_num_in_passive:                     0
% 2.40/0.99  res_num_in_active:                      0
% 2.40/0.99  res_num_of_loops:                       110
% 2.40/0.99  res_forward_subset_subsumed:            11
% 2.40/0.99  res_backward_subset_subsumed:           2
% 2.40/0.99  res_forward_subsumed:                   0
% 2.40/0.99  res_backward_subsumed:                  0
% 2.40/0.99  res_forward_subsumption_resolution:     0
% 2.40/0.99  res_backward_subsumption_resolution:    0
% 2.40/0.99  res_clause_to_clause_subsumption:       525
% 2.40/0.99  res_orphan_elimination:                 0
% 2.40/0.99  res_tautology_del:                      28
% 2.40/0.99  res_num_eq_res_simplified:              0
% 2.40/0.99  res_num_sel_changes:                    0
% 2.40/0.99  res_moves_from_active_to_pass:          0
% 2.40/0.99  
% 2.40/0.99  ------ Superposition
% 2.40/0.99  
% 2.40/0.99  sup_time_total:                         0.
% 2.40/0.99  sup_time_generating:                    0.
% 2.40/0.99  sup_time_sim_full:                      0.
% 2.40/0.99  sup_time_sim_immed:                     0.
% 2.40/0.99  
% 2.40/0.99  sup_num_of_clauses:                     234
% 2.40/0.99  sup_num_in_active:                      73
% 2.40/0.99  sup_num_in_passive:                     161
% 2.40/0.99  sup_num_of_loops:                       76
% 2.40/0.99  sup_fw_superposition:                   102
% 2.40/0.99  sup_bw_superposition:                   134
% 2.40/0.99  sup_immediate_simplified:               17
% 2.40/0.99  sup_given_eliminated:                   0
% 2.40/0.99  comparisons_done:                       0
% 2.40/0.99  comparisons_avoided:                    0
% 2.40/0.99  
% 2.40/0.99  ------ Simplifications
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  sim_fw_subset_subsumed:                 10
% 2.40/0.99  sim_bw_subset_subsumed:                 1
% 2.40/0.99  sim_fw_subsumed:                        3
% 2.40/0.99  sim_bw_subsumed:                        2
% 2.40/0.99  sim_fw_subsumption_res:                 2
% 2.40/0.99  sim_bw_subsumption_res:                 0
% 2.40/0.99  sim_tautology_del:                      9
% 2.40/0.99  sim_eq_tautology_del:                   2
% 2.40/0.99  sim_eq_res_simp:                        2
% 2.40/0.99  sim_fw_demodulated:                     0
% 2.40/0.99  sim_bw_demodulated:                     3
% 2.40/0.99  sim_light_normalised:                   0
% 2.40/0.99  sim_joinable_taut:                      0
% 2.40/0.99  sim_joinable_simp:                      0
% 2.40/0.99  sim_ac_normalised:                      0
% 2.40/0.99  sim_smt_subsumption:                    0
% 2.40/0.99  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:06 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  207 (2367 expanded)
%              Number of clauses        :  139 ( 805 expanded)
%              Number of leaves         :   18 ( 471 expanded)
%              Depth                    :   30
%              Number of atoms          :  696 (11366 expanded)
%              Number of equality atoms :  394 (3406 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK6,X4) != sK5
          | ~ r2_hidden(X4,sK3) )
      & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ! [X4] :
        ( k1_funct_1(sK6,X4) != sK5
        | ~ r2_hidden(X4,sK3) )
    & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f37])).

fof(f63,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

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

fof(f54,plain,(
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
    inference(equality_resolution,[],[f54])).

fof(f66,plain,(
    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f67,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) != sK5
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

cnf(c_8,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_593,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_28])).

cnf(c_594,plain,
    ( r2_hidden(sK0(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_1086,plain,
    ( k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK0(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_595,plain,
    ( k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK0(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_309,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_26])).

cnf(c_310,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_1094,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_1304,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1094])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1432,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1433,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1432])).

cnf(c_1743,plain,
    ( r2_hidden(sK0(sK6,X0),X0) = iProver_top
    | k2_relat_1(sK6) = X0
    | k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1086,c_595,c_1304,c_1433])).

cnf(c_1744,plain,
    ( k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK0(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1743])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_298,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_1095,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_1843,plain,
    ( k1_funct_1(sK6,sK1(sK6,k1_xboole_0)) = sK0(sK6,k1_xboole_0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1744,c_1095])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_494,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_495,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_1092,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_496,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_1934,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1092,c_496,c_1304,c_1433])).

cnf(c_1935,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_1934])).

cnf(c_2284,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(k4_tarski(sK1(sK6,k1_xboole_0),sK0(sK6,k1_xboole_0)),sK6) = iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_1935])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_91,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_92,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_360,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_361,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_1252,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_361])).

cnf(c_833,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1280,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    | X1 != k2_relset_1(sK3,sK4,sK6)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1289,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    | X0 != k2_relset_1(sK3,sK4,sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_1292,plain,
    ( ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    | r2_hidden(sK5,k1_xboole_0)
    | sK5 != sK5
    | k1_xboole_0 != k2_relset_1(sK3,sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_1289])).

cnf(c_831,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1290,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_1379,plain,
    ( ~ r2_hidden(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_832,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1400,plain,
    ( X0 != X1
    | X0 = k2_relset_1(sK3,sK4,sK6)
    | k2_relset_1(sK3,sK4,sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_1910,plain,
    ( X0 = k2_relset_1(sK3,sK4,sK6)
    | X0 != k2_relat_1(sK6)
    | k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_1911,plain,
    ( k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6)
    | k1_xboole_0 = k2_relset_1(sK3,sK4,sK6)
    | k1_xboole_0 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_575,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_576,plain,
    ( r2_hidden(sK1(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK0(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_1087,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_577,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_2001,plain,
    ( r2_hidden(sK0(sK6,X0),X0) = iProver_top
    | r2_hidden(sK1(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | k2_relat_1(sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1087,c_577,c_1304,c_1433])).

cnf(c_2002,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2001])).

cnf(c_2011,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2002,c_1095])).

cnf(c_2742,plain,
    ( X0 != X1
    | X0 = k2_relat_1(sK6)
    | k2_relat_1(sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_2743,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2742])).

cnf(c_5215,plain,
    ( r2_hidden(k4_tarski(sK1(sK6,k1_xboole_0),sK0(sK6,k1_xboole_0)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2284,c_25,c_91,c_92,c_1252,c_1292,c_1290,c_1379,c_1911,c_2011,c_2743])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_324,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_325,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_674,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK4 != X1
    | sK3 != X0
    | sK6 != sK6
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_325])).

cnf(c_675,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_742,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_675])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_369,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_370,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_1255,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_370])).

cnf(c_1344,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_742,c_1255])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_509,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_510,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_1091,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_511,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_1921,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1091,c_511,c_1304,c_1433])).

cnf(c_1922,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1921])).

cnf(c_1929,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_1922])).

cnf(c_1096,plain,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1276,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1252,c_1096])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_524,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_525,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_1090,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_526,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1618,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1090,c_526,c_1304,c_1433])).

cnf(c_1619,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1618])).

cnf(c_1626,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_1276,c_1619])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK6,X0) != sK5 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1097,plain,
    ( k1_funct_1(sK6,X0) != sK5
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2127,plain,
    ( r2_hidden(sK2(sK6,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1626,c_1097])).

cnf(c_2125,plain,
    ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1626,c_1935])).

cnf(c_1760,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | ~ r2_hidden(sK5,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_1761,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK5,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1760])).

cnf(c_2376,plain,
    ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2125,c_1276,c_1304,c_1433,c_1761])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_479,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_480,plain,
    ( r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_1093,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_481,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_1734,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1093,c_481,c_1304,c_1433])).

cnf(c_1735,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1734])).

cnf(c_2381,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2376,c_1735])).

cnf(c_2388,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_2381])).

cnf(c_2816,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1929,c_2127,c_2388])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_395,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_396,plain,
    ( ~ v1_funct_2(sK6,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_685,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK4 != k1_xboole_0
    | sK3 != X0
    | sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_396])).

cnf(c_686,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK4 != k1_xboole_0
    | sK6 = k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1174,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k1_xboole_0)
    | sK4 != k1_xboole_0
    | sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_686,c_2])).

cnf(c_2819,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK3 = k1_xboole_0
    | sK6 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2816,c_1174])).

cnf(c_2872,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2819])).

cnf(c_2876,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2872,c_2])).

cnf(c_2877,plain,
    ( sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2876])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_413,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_414,plain,
    ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK6) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_699,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK4 != X0
    | sK3 != k1_xboole_0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_414])).

cnf(c_700,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_1155,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_700,c_3])).

cnf(c_2820,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2816,c_1155])).

cnf(c_1410,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_370])).

cnf(c_2822,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2816,c_1410])).

cnf(c_2856,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2822,c_2])).

cnf(c_2857,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution_simp,[status(thm)],[c_2856])).

cnf(c_2864,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2820,c_2857])).

cnf(c_2868,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2864,c_2])).

cnf(c_2869,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2868])).

cnf(c_3547,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2877,c_2869])).

cnf(c_4226,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3547,c_2381])).

cnf(c_4266,plain,
    ( sK6 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4226,c_1095])).

cnf(c_5219,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5215,c_4266])).

cnf(c_5221,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5219,c_1095])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:01:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.19/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/1.03  
% 2.19/1.03  ------  iProver source info
% 2.19/1.03  
% 2.19/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.19/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/1.03  git: non_committed_changes: false
% 2.19/1.03  git: last_make_outside_of_git: false
% 2.19/1.03  
% 2.19/1.03  ------ 
% 2.19/1.03  
% 2.19/1.03  ------ Input Options
% 2.19/1.03  
% 2.19/1.03  --out_options                           all
% 2.19/1.03  --tptp_safe_out                         true
% 2.19/1.03  --problem_path                          ""
% 2.19/1.03  --include_path                          ""
% 2.19/1.03  --clausifier                            res/vclausify_rel
% 2.19/1.03  --clausifier_options                    --mode clausify
% 2.19/1.03  --stdin                                 false
% 2.19/1.03  --stats_out                             all
% 2.19/1.03  
% 2.19/1.03  ------ General Options
% 2.19/1.03  
% 2.19/1.03  --fof                                   false
% 2.19/1.03  --time_out_real                         305.
% 2.19/1.03  --time_out_virtual                      -1.
% 2.19/1.03  --symbol_type_check                     false
% 2.19/1.03  --clausify_out                          false
% 2.19/1.03  --sig_cnt_out                           false
% 2.19/1.03  --trig_cnt_out                          false
% 2.19/1.03  --trig_cnt_out_tolerance                1.
% 2.19/1.03  --trig_cnt_out_sk_spl                   false
% 2.19/1.03  --abstr_cl_out                          false
% 2.19/1.03  
% 2.19/1.03  ------ Global Options
% 2.19/1.03  
% 2.19/1.03  --schedule                              default
% 2.19/1.03  --add_important_lit                     false
% 2.19/1.03  --prop_solver_per_cl                    1000
% 2.19/1.03  --min_unsat_core                        false
% 2.19/1.03  --soft_assumptions                      false
% 2.19/1.03  --soft_lemma_size                       3
% 2.19/1.03  --prop_impl_unit_size                   0
% 2.19/1.03  --prop_impl_unit                        []
% 2.19/1.03  --share_sel_clauses                     true
% 2.19/1.03  --reset_solvers                         false
% 2.19/1.03  --bc_imp_inh                            [conj_cone]
% 2.19/1.03  --conj_cone_tolerance                   3.
% 2.19/1.03  --extra_neg_conj                        none
% 2.19/1.03  --large_theory_mode                     true
% 2.19/1.03  --prolific_symb_bound                   200
% 2.19/1.03  --lt_threshold                          2000
% 2.19/1.03  --clause_weak_htbl                      true
% 2.19/1.03  --gc_record_bc_elim                     false
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing Options
% 2.19/1.03  
% 2.19/1.03  --preprocessing_flag                    true
% 2.19/1.03  --time_out_prep_mult                    0.1
% 2.19/1.03  --splitting_mode                        input
% 2.19/1.03  --splitting_grd                         true
% 2.19/1.03  --splitting_cvd                         false
% 2.19/1.03  --splitting_cvd_svl                     false
% 2.19/1.03  --splitting_nvd                         32
% 2.19/1.03  --sub_typing                            true
% 2.19/1.03  --prep_gs_sim                           true
% 2.19/1.03  --prep_unflatten                        true
% 2.19/1.03  --prep_res_sim                          true
% 2.19/1.03  --prep_upred                            true
% 2.19/1.03  --prep_sem_filter                       exhaustive
% 2.19/1.03  --prep_sem_filter_out                   false
% 2.19/1.03  --pred_elim                             true
% 2.19/1.03  --res_sim_input                         true
% 2.19/1.03  --eq_ax_congr_red                       true
% 2.19/1.03  --pure_diseq_elim                       true
% 2.19/1.03  --brand_transform                       false
% 2.19/1.03  --non_eq_to_eq                          false
% 2.19/1.03  --prep_def_merge                        true
% 2.19/1.03  --prep_def_merge_prop_impl              false
% 2.19/1.03  --prep_def_merge_mbd                    true
% 2.19/1.03  --prep_def_merge_tr_red                 false
% 2.19/1.03  --prep_def_merge_tr_cl                  false
% 2.19/1.03  --smt_preprocessing                     true
% 2.19/1.03  --smt_ac_axioms                         fast
% 2.19/1.03  --preprocessed_out                      false
% 2.19/1.03  --preprocessed_stats                    false
% 2.19/1.03  
% 2.19/1.03  ------ Abstraction refinement Options
% 2.19/1.03  
% 2.19/1.03  --abstr_ref                             []
% 2.19/1.03  --abstr_ref_prep                        false
% 2.19/1.03  --abstr_ref_until_sat                   false
% 2.19/1.03  --abstr_ref_sig_restrict                funpre
% 2.19/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.03  --abstr_ref_under                       []
% 2.19/1.03  
% 2.19/1.03  ------ SAT Options
% 2.19/1.03  
% 2.19/1.03  --sat_mode                              false
% 2.19/1.03  --sat_fm_restart_options                ""
% 2.19/1.03  --sat_gr_def                            false
% 2.19/1.03  --sat_epr_types                         true
% 2.19/1.03  --sat_non_cyclic_types                  false
% 2.19/1.03  --sat_finite_models                     false
% 2.19/1.03  --sat_fm_lemmas                         false
% 2.19/1.03  --sat_fm_prep                           false
% 2.19/1.03  --sat_fm_uc_incr                        true
% 2.19/1.03  --sat_out_model                         small
% 2.19/1.03  --sat_out_clauses                       false
% 2.19/1.03  
% 2.19/1.03  ------ QBF Options
% 2.19/1.03  
% 2.19/1.03  --qbf_mode                              false
% 2.19/1.03  --qbf_elim_univ                         false
% 2.19/1.03  --qbf_dom_inst                          none
% 2.19/1.03  --qbf_dom_pre_inst                      false
% 2.19/1.03  --qbf_sk_in                             false
% 2.19/1.03  --qbf_pred_elim                         true
% 2.19/1.03  --qbf_split                             512
% 2.19/1.03  
% 2.19/1.03  ------ BMC1 Options
% 2.19/1.03  
% 2.19/1.03  --bmc1_incremental                      false
% 2.19/1.03  --bmc1_axioms                           reachable_all
% 2.19/1.03  --bmc1_min_bound                        0
% 2.19/1.03  --bmc1_max_bound                        -1
% 2.19/1.03  --bmc1_max_bound_default                -1
% 2.19/1.03  --bmc1_symbol_reachability              true
% 2.19/1.03  --bmc1_property_lemmas                  false
% 2.19/1.03  --bmc1_k_induction                      false
% 2.19/1.03  --bmc1_non_equiv_states                 false
% 2.19/1.03  --bmc1_deadlock                         false
% 2.19/1.03  --bmc1_ucm                              false
% 2.19/1.03  --bmc1_add_unsat_core                   none
% 2.19/1.03  --bmc1_unsat_core_children              false
% 2.19/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.03  --bmc1_out_stat                         full
% 2.19/1.03  --bmc1_ground_init                      false
% 2.19/1.03  --bmc1_pre_inst_next_state              false
% 2.19/1.03  --bmc1_pre_inst_state                   false
% 2.19/1.03  --bmc1_pre_inst_reach_state             false
% 2.19/1.03  --bmc1_out_unsat_core                   false
% 2.19/1.03  --bmc1_aig_witness_out                  false
% 2.19/1.03  --bmc1_verbose                          false
% 2.19/1.03  --bmc1_dump_clauses_tptp                false
% 2.19/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.03  --bmc1_dump_file                        -
% 2.19/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.03  --bmc1_ucm_extend_mode                  1
% 2.19/1.03  --bmc1_ucm_init_mode                    2
% 2.19/1.03  --bmc1_ucm_cone_mode                    none
% 2.19/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.03  --bmc1_ucm_relax_model                  4
% 2.19/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.03  --bmc1_ucm_layered_model                none
% 2.19/1.03  --bmc1_ucm_max_lemma_size               10
% 2.19/1.03  
% 2.19/1.03  ------ AIG Options
% 2.19/1.03  
% 2.19/1.03  --aig_mode                              false
% 2.19/1.03  
% 2.19/1.03  ------ Instantiation Options
% 2.19/1.03  
% 2.19/1.03  --instantiation_flag                    true
% 2.19/1.03  --inst_sos_flag                         false
% 2.19/1.03  --inst_sos_phase                        true
% 2.19/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel_side                     num_symb
% 2.19/1.03  --inst_solver_per_active                1400
% 2.19/1.03  --inst_solver_calls_frac                1.
% 2.19/1.03  --inst_passive_queue_type               priority_queues
% 2.19/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.03  --inst_passive_queues_freq              [25;2]
% 2.19/1.03  --inst_dismatching                      true
% 2.19/1.03  --inst_eager_unprocessed_to_passive     true
% 2.19/1.03  --inst_prop_sim_given                   true
% 2.19/1.03  --inst_prop_sim_new                     false
% 2.19/1.03  --inst_subs_new                         false
% 2.19/1.03  --inst_eq_res_simp                      false
% 2.19/1.03  --inst_subs_given                       false
% 2.19/1.03  --inst_orphan_elimination               true
% 2.19/1.03  --inst_learning_loop_flag               true
% 2.19/1.03  --inst_learning_start                   3000
% 2.19/1.03  --inst_learning_factor                  2
% 2.19/1.03  --inst_start_prop_sim_after_learn       3
% 2.19/1.03  --inst_sel_renew                        solver
% 2.19/1.03  --inst_lit_activity_flag                true
% 2.19/1.03  --inst_restr_to_given                   false
% 2.19/1.03  --inst_activity_threshold               500
% 2.19/1.03  --inst_out_proof                        true
% 2.19/1.03  
% 2.19/1.03  ------ Resolution Options
% 2.19/1.03  
% 2.19/1.03  --resolution_flag                       true
% 2.19/1.03  --res_lit_sel                           adaptive
% 2.19/1.03  --res_lit_sel_side                      none
% 2.19/1.03  --res_ordering                          kbo
% 2.19/1.03  --res_to_prop_solver                    active
% 2.19/1.03  --res_prop_simpl_new                    false
% 2.19/1.03  --res_prop_simpl_given                  true
% 2.19/1.03  --res_passive_queue_type                priority_queues
% 2.19/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.03  --res_passive_queues_freq               [15;5]
% 2.19/1.03  --res_forward_subs                      full
% 2.19/1.03  --res_backward_subs                     full
% 2.19/1.03  --res_forward_subs_resolution           true
% 2.19/1.03  --res_backward_subs_resolution          true
% 2.19/1.03  --res_orphan_elimination                true
% 2.19/1.03  --res_time_limit                        2.
% 2.19/1.03  --res_out_proof                         true
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Options
% 2.19/1.03  
% 2.19/1.03  --superposition_flag                    true
% 2.19/1.03  --sup_passive_queue_type                priority_queues
% 2.19/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.03  --demod_completeness_check              fast
% 2.19/1.03  --demod_use_ground                      true
% 2.19/1.03  --sup_to_prop_solver                    passive
% 2.19/1.03  --sup_prop_simpl_new                    true
% 2.19/1.03  --sup_prop_simpl_given                  true
% 2.19/1.03  --sup_fun_splitting                     false
% 2.19/1.03  --sup_smt_interval                      50000
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Simplification Setup
% 2.19/1.03  
% 2.19/1.03  --sup_indices_passive                   []
% 2.19/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_full_bw                           [BwDemod]
% 2.19/1.03  --sup_immed_triv                        [TrivRules]
% 2.19/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_immed_bw_main                     []
% 2.19/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  
% 2.19/1.03  ------ Combination Options
% 2.19/1.03  
% 2.19/1.03  --comb_res_mult                         3
% 2.19/1.03  --comb_sup_mult                         2
% 2.19/1.03  --comb_inst_mult                        10
% 2.19/1.03  
% 2.19/1.03  ------ Debug Options
% 2.19/1.03  
% 2.19/1.03  --dbg_backtrace                         false
% 2.19/1.03  --dbg_dump_prop_clauses                 false
% 2.19/1.03  --dbg_dump_prop_clauses_file            -
% 2.19/1.03  --dbg_out_stat                          false
% 2.19/1.03  ------ Parsing...
% 2.19/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/1.03  ------ Proving...
% 2.19/1.03  ------ Problem Properties 
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  clauses                                 22
% 2.19/1.03  conjectures                             2
% 2.19/1.03  EPR                                     1
% 2.19/1.03  Horn                                    17
% 2.19/1.03  unary                                   5
% 2.19/1.03  binary                                  4
% 2.19/1.03  lits                                    57
% 2.19/1.03  lits eq                                 27
% 2.19/1.03  fd_pure                                 0
% 2.19/1.03  fd_pseudo                               0
% 2.19/1.03  fd_cond                                 4
% 2.19/1.03  fd_pseudo_cond                          1
% 2.19/1.03  AC symbols                              0
% 2.19/1.03  
% 2.19/1.03  ------ Schedule dynamic 5 is on 
% 2.19/1.03  
% 2.19/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  ------ 
% 2.19/1.03  Current options:
% 2.19/1.03  ------ 
% 2.19/1.03  
% 2.19/1.03  ------ Input Options
% 2.19/1.03  
% 2.19/1.03  --out_options                           all
% 2.19/1.03  --tptp_safe_out                         true
% 2.19/1.03  --problem_path                          ""
% 2.19/1.03  --include_path                          ""
% 2.19/1.03  --clausifier                            res/vclausify_rel
% 2.19/1.03  --clausifier_options                    --mode clausify
% 2.19/1.03  --stdin                                 false
% 2.19/1.03  --stats_out                             all
% 2.19/1.03  
% 2.19/1.03  ------ General Options
% 2.19/1.03  
% 2.19/1.03  --fof                                   false
% 2.19/1.03  --time_out_real                         305.
% 2.19/1.03  --time_out_virtual                      -1.
% 2.19/1.03  --symbol_type_check                     false
% 2.19/1.03  --clausify_out                          false
% 2.19/1.03  --sig_cnt_out                           false
% 2.19/1.03  --trig_cnt_out                          false
% 2.19/1.03  --trig_cnt_out_tolerance                1.
% 2.19/1.03  --trig_cnt_out_sk_spl                   false
% 2.19/1.03  --abstr_cl_out                          false
% 2.19/1.03  
% 2.19/1.03  ------ Global Options
% 2.19/1.03  
% 2.19/1.03  --schedule                              default
% 2.19/1.03  --add_important_lit                     false
% 2.19/1.03  --prop_solver_per_cl                    1000
% 2.19/1.03  --min_unsat_core                        false
% 2.19/1.03  --soft_assumptions                      false
% 2.19/1.03  --soft_lemma_size                       3
% 2.19/1.03  --prop_impl_unit_size                   0
% 2.19/1.03  --prop_impl_unit                        []
% 2.19/1.03  --share_sel_clauses                     true
% 2.19/1.03  --reset_solvers                         false
% 2.19/1.03  --bc_imp_inh                            [conj_cone]
% 2.19/1.03  --conj_cone_tolerance                   3.
% 2.19/1.03  --extra_neg_conj                        none
% 2.19/1.03  --large_theory_mode                     true
% 2.19/1.03  --prolific_symb_bound                   200
% 2.19/1.03  --lt_threshold                          2000
% 2.19/1.03  --clause_weak_htbl                      true
% 2.19/1.03  --gc_record_bc_elim                     false
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing Options
% 2.19/1.03  
% 2.19/1.03  --preprocessing_flag                    true
% 2.19/1.03  --time_out_prep_mult                    0.1
% 2.19/1.03  --splitting_mode                        input
% 2.19/1.03  --splitting_grd                         true
% 2.19/1.03  --splitting_cvd                         false
% 2.19/1.03  --splitting_cvd_svl                     false
% 2.19/1.03  --splitting_nvd                         32
% 2.19/1.03  --sub_typing                            true
% 2.19/1.03  --prep_gs_sim                           true
% 2.19/1.03  --prep_unflatten                        true
% 2.19/1.03  --prep_res_sim                          true
% 2.19/1.03  --prep_upred                            true
% 2.19/1.03  --prep_sem_filter                       exhaustive
% 2.19/1.03  --prep_sem_filter_out                   false
% 2.19/1.03  --pred_elim                             true
% 2.19/1.03  --res_sim_input                         true
% 2.19/1.03  --eq_ax_congr_red                       true
% 2.19/1.03  --pure_diseq_elim                       true
% 2.19/1.03  --brand_transform                       false
% 2.19/1.03  --non_eq_to_eq                          false
% 2.19/1.03  --prep_def_merge                        true
% 2.19/1.03  --prep_def_merge_prop_impl              false
% 2.19/1.03  --prep_def_merge_mbd                    true
% 2.19/1.03  --prep_def_merge_tr_red                 false
% 2.19/1.03  --prep_def_merge_tr_cl                  false
% 2.19/1.03  --smt_preprocessing                     true
% 2.19/1.03  --smt_ac_axioms                         fast
% 2.19/1.03  --preprocessed_out                      false
% 2.19/1.03  --preprocessed_stats                    false
% 2.19/1.03  
% 2.19/1.03  ------ Abstraction refinement Options
% 2.19/1.03  
% 2.19/1.03  --abstr_ref                             []
% 2.19/1.03  --abstr_ref_prep                        false
% 2.19/1.03  --abstr_ref_until_sat                   false
% 2.19/1.03  --abstr_ref_sig_restrict                funpre
% 2.19/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.03  --abstr_ref_under                       []
% 2.19/1.03  
% 2.19/1.03  ------ SAT Options
% 2.19/1.03  
% 2.19/1.03  --sat_mode                              false
% 2.19/1.03  --sat_fm_restart_options                ""
% 2.19/1.03  --sat_gr_def                            false
% 2.19/1.03  --sat_epr_types                         true
% 2.19/1.03  --sat_non_cyclic_types                  false
% 2.19/1.03  --sat_finite_models                     false
% 2.19/1.03  --sat_fm_lemmas                         false
% 2.19/1.03  --sat_fm_prep                           false
% 2.19/1.03  --sat_fm_uc_incr                        true
% 2.19/1.03  --sat_out_model                         small
% 2.19/1.03  --sat_out_clauses                       false
% 2.19/1.03  
% 2.19/1.03  ------ QBF Options
% 2.19/1.03  
% 2.19/1.03  --qbf_mode                              false
% 2.19/1.03  --qbf_elim_univ                         false
% 2.19/1.03  --qbf_dom_inst                          none
% 2.19/1.03  --qbf_dom_pre_inst                      false
% 2.19/1.03  --qbf_sk_in                             false
% 2.19/1.03  --qbf_pred_elim                         true
% 2.19/1.03  --qbf_split                             512
% 2.19/1.03  
% 2.19/1.03  ------ BMC1 Options
% 2.19/1.03  
% 2.19/1.03  --bmc1_incremental                      false
% 2.19/1.03  --bmc1_axioms                           reachable_all
% 2.19/1.03  --bmc1_min_bound                        0
% 2.19/1.03  --bmc1_max_bound                        -1
% 2.19/1.03  --bmc1_max_bound_default                -1
% 2.19/1.03  --bmc1_symbol_reachability              true
% 2.19/1.03  --bmc1_property_lemmas                  false
% 2.19/1.03  --bmc1_k_induction                      false
% 2.19/1.03  --bmc1_non_equiv_states                 false
% 2.19/1.03  --bmc1_deadlock                         false
% 2.19/1.03  --bmc1_ucm                              false
% 2.19/1.03  --bmc1_add_unsat_core                   none
% 2.19/1.03  --bmc1_unsat_core_children              false
% 2.19/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.03  --bmc1_out_stat                         full
% 2.19/1.03  --bmc1_ground_init                      false
% 2.19/1.03  --bmc1_pre_inst_next_state              false
% 2.19/1.03  --bmc1_pre_inst_state                   false
% 2.19/1.03  --bmc1_pre_inst_reach_state             false
% 2.19/1.03  --bmc1_out_unsat_core                   false
% 2.19/1.03  --bmc1_aig_witness_out                  false
% 2.19/1.03  --bmc1_verbose                          false
% 2.19/1.03  --bmc1_dump_clauses_tptp                false
% 2.19/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.03  --bmc1_dump_file                        -
% 2.19/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.03  --bmc1_ucm_extend_mode                  1
% 2.19/1.03  --bmc1_ucm_init_mode                    2
% 2.19/1.03  --bmc1_ucm_cone_mode                    none
% 2.19/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.03  --bmc1_ucm_relax_model                  4
% 2.19/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.03  --bmc1_ucm_layered_model                none
% 2.19/1.03  --bmc1_ucm_max_lemma_size               10
% 2.19/1.03  
% 2.19/1.03  ------ AIG Options
% 2.19/1.03  
% 2.19/1.03  --aig_mode                              false
% 2.19/1.03  
% 2.19/1.03  ------ Instantiation Options
% 2.19/1.03  
% 2.19/1.03  --instantiation_flag                    true
% 2.19/1.03  --inst_sos_flag                         false
% 2.19/1.03  --inst_sos_phase                        true
% 2.19/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel_side                     none
% 2.19/1.03  --inst_solver_per_active                1400
% 2.19/1.03  --inst_solver_calls_frac                1.
% 2.19/1.03  --inst_passive_queue_type               priority_queues
% 2.19/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.03  --inst_passive_queues_freq              [25;2]
% 2.19/1.03  --inst_dismatching                      true
% 2.19/1.03  --inst_eager_unprocessed_to_passive     true
% 2.19/1.03  --inst_prop_sim_given                   true
% 2.19/1.03  --inst_prop_sim_new                     false
% 2.19/1.03  --inst_subs_new                         false
% 2.19/1.03  --inst_eq_res_simp                      false
% 2.19/1.03  --inst_subs_given                       false
% 2.19/1.03  --inst_orphan_elimination               true
% 2.19/1.03  --inst_learning_loop_flag               true
% 2.19/1.03  --inst_learning_start                   3000
% 2.19/1.03  --inst_learning_factor                  2
% 2.19/1.03  --inst_start_prop_sim_after_learn       3
% 2.19/1.03  --inst_sel_renew                        solver
% 2.19/1.03  --inst_lit_activity_flag                true
% 2.19/1.03  --inst_restr_to_given                   false
% 2.19/1.03  --inst_activity_threshold               500
% 2.19/1.03  --inst_out_proof                        true
% 2.19/1.03  
% 2.19/1.03  ------ Resolution Options
% 2.19/1.03  
% 2.19/1.03  --resolution_flag                       false
% 2.19/1.03  --res_lit_sel                           adaptive
% 2.19/1.03  --res_lit_sel_side                      none
% 2.19/1.03  --res_ordering                          kbo
% 2.19/1.03  --res_to_prop_solver                    active
% 2.19/1.03  --res_prop_simpl_new                    false
% 2.19/1.03  --res_prop_simpl_given                  true
% 2.19/1.03  --res_passive_queue_type                priority_queues
% 2.19/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.03  --res_passive_queues_freq               [15;5]
% 2.19/1.03  --res_forward_subs                      full
% 2.19/1.03  --res_backward_subs                     full
% 2.19/1.03  --res_forward_subs_resolution           true
% 2.19/1.03  --res_backward_subs_resolution          true
% 2.19/1.03  --res_orphan_elimination                true
% 2.19/1.03  --res_time_limit                        2.
% 2.19/1.03  --res_out_proof                         true
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Options
% 2.19/1.03  
% 2.19/1.03  --superposition_flag                    true
% 2.19/1.03  --sup_passive_queue_type                priority_queues
% 2.19/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.03  --demod_completeness_check              fast
% 2.19/1.03  --demod_use_ground                      true
% 2.19/1.03  --sup_to_prop_solver                    passive
% 2.19/1.03  --sup_prop_simpl_new                    true
% 2.19/1.03  --sup_prop_simpl_given                  true
% 2.19/1.03  --sup_fun_splitting                     false
% 2.19/1.03  --sup_smt_interval                      50000
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Simplification Setup
% 2.19/1.03  
% 2.19/1.03  --sup_indices_passive                   []
% 2.19/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_full_bw                           [BwDemod]
% 2.19/1.03  --sup_immed_triv                        [TrivRules]
% 2.19/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_immed_bw_main                     []
% 2.19/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  
% 2.19/1.03  ------ Combination Options
% 2.19/1.03  
% 2.19/1.03  --comb_res_mult                         3
% 2.19/1.03  --comb_sup_mult                         2
% 2.19/1.03  --comb_inst_mult                        10
% 2.19/1.03  
% 2.19/1.03  ------ Debug Options
% 2.19/1.03  
% 2.19/1.03  --dbg_backtrace                         false
% 2.19/1.03  --dbg_dump_prop_clauses                 false
% 2.19/1.03  --dbg_dump_prop_clauses_file            -
% 2.19/1.03  --dbg_out_stat                          false
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  ------ Proving...
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  % SZS status Theorem for theBenchmark.p
% 2.19/1.03  
% 2.19/1.03   Resolution empty clause
% 2.19/1.03  
% 2.19/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  fof(f6,axiom,(
% 2.19/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f16,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f6])).
% 2.19/1.03  
% 2.19/1.03  fof(f17,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/1.03    inference(flattening,[],[f16])).
% 2.19/1.03  
% 2.19/1.03  fof(f28,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/1.03    inference(nnf_transformation,[],[f17])).
% 2.19/1.03  
% 2.19/1.03  fof(f29,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/1.03    inference(rectify,[],[f28])).
% 2.19/1.03  
% 2.19/1.03  fof(f32,plain,(
% 2.19/1.03    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f31,plain,(
% 2.19/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f30,plain,(
% 2.19/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f33,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).
% 2.19/1.03  
% 2.19/1.03  fof(f50,plain,(
% 2.19/1.03    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f33])).
% 2.19/1.03  
% 2.19/1.03  fof(f11,conjecture,(
% 2.19/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f12,negated_conjecture,(
% 2.19/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 2.19/1.03    inference(negated_conjecture,[],[f11])).
% 2.19/1.03  
% 2.19/1.03  fof(f24,plain,(
% 2.19/1.03    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.19/1.03    inference(ennf_transformation,[],[f12])).
% 2.19/1.03  
% 2.19/1.03  fof(f25,plain,(
% 2.19/1.03    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.19/1.03    inference(flattening,[],[f24])).
% 2.19/1.03  
% 2.19/1.03  fof(f37,plain,(
% 2.19/1.03    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f38,plain,(
% 2.19/1.03    ! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 2.19/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f37])).
% 2.19/1.03  
% 2.19/1.03  fof(f63,plain,(
% 2.19/1.03    v1_funct_1(sK6)),
% 2.19/1.03    inference(cnf_transformation,[],[f38])).
% 2.19/1.03  
% 2.19/1.03  fof(f4,axiom,(
% 2.19/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f15,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.19/1.03    inference(ennf_transformation,[],[f4])).
% 2.19/1.03  
% 2.19/1.03  fof(f44,plain,(
% 2.19/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f15])).
% 2.19/1.03  
% 2.19/1.03  fof(f65,plain,(
% 2.19/1.03    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.19/1.03    inference(cnf_transformation,[],[f38])).
% 2.19/1.03  
% 2.19/1.03  fof(f5,axiom,(
% 2.19/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f45,plain,(
% 2.19/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.19/1.03    inference(cnf_transformation,[],[f5])).
% 2.19/1.03  
% 2.19/1.03  fof(f1,axiom,(
% 2.19/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f13,plain,(
% 2.19/1.03    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.19/1.03    inference(unused_predicate_definition_removal,[],[f1])).
% 2.19/1.03  
% 2.19/1.03  fof(f14,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.19/1.03    inference(ennf_transformation,[],[f13])).
% 2.19/1.03  
% 2.19/1.03  fof(f39,plain,(
% 2.19/1.03    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f14])).
% 2.19/1.03  
% 2.19/1.03  fof(f2,axiom,(
% 2.19/1.03    v1_xboole_0(k1_xboole_0)),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f40,plain,(
% 2.19/1.03    v1_xboole_0(k1_xboole_0)),
% 2.19/1.03    inference(cnf_transformation,[],[f2])).
% 2.19/1.03  
% 2.19/1.03  fof(f7,axiom,(
% 2.19/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f18,plain,(
% 2.19/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.19/1.03    inference(ennf_transformation,[],[f7])).
% 2.19/1.03  
% 2.19/1.03  fof(f19,plain,(
% 2.19/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.19/1.03    inference(flattening,[],[f18])).
% 2.19/1.03  
% 2.19/1.03  fof(f34,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.19/1.03    inference(nnf_transformation,[],[f19])).
% 2.19/1.03  
% 2.19/1.03  fof(f35,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.19/1.03    inference(flattening,[],[f34])).
% 2.19/1.03  
% 2.19/1.03  fof(f54,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f35])).
% 2.19/1.03  
% 2.19/1.03  fof(f74,plain,(
% 2.19/1.03    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.19/1.03    inference(equality_resolution,[],[f54])).
% 2.19/1.03  
% 2.19/1.03  fof(f66,plain,(
% 2.19/1.03    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))),
% 2.19/1.03    inference(cnf_transformation,[],[f38])).
% 2.19/1.03  
% 2.19/1.03  fof(f3,axiom,(
% 2.19/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f26,plain,(
% 2.19/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.19/1.03    inference(nnf_transformation,[],[f3])).
% 2.19/1.03  
% 2.19/1.03  fof(f27,plain,(
% 2.19/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.19/1.03    inference(flattening,[],[f26])).
% 2.19/1.03  
% 2.19/1.03  fof(f41,plain,(
% 2.19/1.03    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f27])).
% 2.19/1.03  
% 2.19/1.03  fof(f42,plain,(
% 2.19/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.19/1.03    inference(cnf_transformation,[],[f27])).
% 2.19/1.03  
% 2.19/1.03  fof(f69,plain,(
% 2.19/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.19/1.03    inference(equality_resolution,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f9,axiom,(
% 2.19/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f21,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.03    inference(ennf_transformation,[],[f9])).
% 2.19/1.03  
% 2.19/1.03  fof(f56,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.03    inference(cnf_transformation,[],[f21])).
% 2.19/1.03  
% 2.19/1.03  fof(f49,plain,(
% 2.19/1.03    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f33])).
% 2.19/1.03  
% 2.19/1.03  fof(f64,plain,(
% 2.19/1.03    v1_funct_2(sK6,sK3,sK4)),
% 2.19/1.03    inference(cnf_transformation,[],[f38])).
% 2.19/1.03  
% 2.19/1.03  fof(f10,axiom,(
% 2.19/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f22,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.03    inference(ennf_transformation,[],[f10])).
% 2.19/1.03  
% 2.19/1.03  fof(f23,plain,(
% 2.19/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.03    inference(flattening,[],[f22])).
% 2.19/1.03  
% 2.19/1.03  fof(f36,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.03    inference(nnf_transformation,[],[f23])).
% 2.19/1.03  
% 2.19/1.03  fof(f57,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.03    inference(cnf_transformation,[],[f36])).
% 2.19/1.03  
% 2.19/1.03  fof(f8,axiom,(
% 2.19/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.19/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f20,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/1.03    inference(ennf_transformation,[],[f8])).
% 2.19/1.03  
% 2.19/1.03  fof(f55,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.03    inference(cnf_transformation,[],[f20])).
% 2.19/1.03  
% 2.19/1.03  fof(f46,plain,(
% 2.19/1.03    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f33])).
% 2.19/1.03  
% 2.19/1.03  fof(f73,plain,(
% 2.19/1.03    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/1.03    inference(equality_resolution,[],[f46])).
% 2.19/1.03  
% 2.19/1.03  fof(f47,plain,(
% 2.19/1.03    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f33])).
% 2.19/1.03  
% 2.19/1.03  fof(f72,plain,(
% 2.19/1.03    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/1.03    inference(equality_resolution,[],[f47])).
% 2.19/1.03  
% 2.19/1.03  fof(f67,plain,(
% 2.19/1.03    ( ! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f38])).
% 2.19/1.03  
% 2.19/1.03  fof(f52,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f35])).
% 2.19/1.03  
% 2.19/1.03  fof(f61,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.03    inference(cnf_transformation,[],[f36])).
% 2.19/1.03  
% 2.19/1.03  fof(f77,plain,(
% 2.19/1.03    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.19/1.03    inference(equality_resolution,[],[f61])).
% 2.19/1.03  
% 2.19/1.03  fof(f43,plain,(
% 2.19/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.19/1.03    inference(cnf_transformation,[],[f27])).
% 2.19/1.03  
% 2.19/1.03  fof(f68,plain,(
% 2.19/1.03    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.19/1.03    inference(equality_resolution,[],[f43])).
% 2.19/1.03  
% 2.19/1.03  fof(f58,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/1.03    inference(cnf_transformation,[],[f36])).
% 2.19/1.03  
% 2.19/1.03  fof(f79,plain,(
% 2.19/1.03    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.19/1.03    inference(equality_resolution,[],[f58])).
% 2.19/1.03  
% 2.19/1.03  cnf(c_8,plain,
% 2.19/1.03      ( r2_hidden(sK0(X0,X1),X1)
% 2.19/1.03      | ~ v1_funct_1(X0)
% 2.19/1.03      | ~ v1_relat_1(X0)
% 2.19/1.03      | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
% 2.19/1.03      | k2_relat_1(X0) = X1 ),
% 2.19/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_28,negated_conjecture,
% 2.19/1.03      ( v1_funct_1(sK6) ),
% 2.19/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_593,plain,
% 2.19/1.03      ( r2_hidden(sK0(X0,X1),X1)
% 2.19/1.03      | ~ v1_relat_1(X0)
% 2.19/1.03      | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
% 2.19/1.03      | k2_relat_1(X0) = X1
% 2.19/1.03      | sK6 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_28]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_594,plain,
% 2.19/1.03      ( r2_hidden(sK0(sK6,X0),X0)
% 2.19/1.03      | ~ v1_relat_1(sK6)
% 2.19/1.03      | k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0)
% 2.19/1.03      | k2_relat_1(sK6) = X0 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_593]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1086,plain,
% 2.19/1.03      ( k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0)
% 2.19/1.03      | k2_relat_1(sK6) = X0
% 2.19/1.03      | r2_hidden(sK0(sK6,X0),X0) = iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_595,plain,
% 2.19/1.03      ( k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0)
% 2.19/1.03      | k2_relat_1(sK6) = X0
% 2.19/1.03      | r2_hidden(sK0(sK6,X0),X0) = iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_5,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_26,negated_conjecture,
% 2.19/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.19/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_309,plain,
% 2.19/1.03      ( ~ v1_relat_1(X0)
% 2.19/1.03      | v1_relat_1(X1)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
% 2.19/1.03      | sK6 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_26]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_310,plain,
% 2.19/1.03      ( ~ v1_relat_1(X0)
% 2.19/1.03      | v1_relat_1(sK6)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_309]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1094,plain,
% 2.19/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
% 2.19/1.03      | v1_relat_1(X0) != iProver_top
% 2.19/1.03      | v1_relat_1(sK6) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1304,plain,
% 2.19/1.03      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 2.19/1.03      | v1_relat_1(sK6) = iProver_top ),
% 2.19/1.03      inference(equality_resolution,[status(thm)],[c_1094]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_6,plain,
% 2.19/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.19/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1432,plain,
% 2.19/1.03      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1433,plain,
% 2.19/1.03      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_1432]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1743,plain,
% 2.19/1.03      ( r2_hidden(sK0(sK6,X0),X0) = iProver_top
% 2.19/1.03      | k2_relat_1(sK6) = X0
% 2.19/1.03      | k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0) ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1086,c_595,c_1304,c_1433]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1744,plain,
% 2.19/1.03      ( k1_funct_1(sK6,sK1(sK6,X0)) = sK0(sK6,X0)
% 2.19/1.03      | k2_relat_1(sK6) = X0
% 2.19/1.03      | r2_hidden(sK0(sK6,X0),X0) = iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_1743]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_0,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f39]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1,plain,
% 2.19/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_298,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_299,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_298]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1095,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1843,plain,
% 2.19/1.03      ( k1_funct_1(sK6,sK1(sK6,k1_xboole_0)) = sK0(sK6,k1_xboole_0)
% 2.19/1.03      | k2_relat_1(sK6) = k1_xboole_0 ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1744,c_1095]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_13,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.19/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.19/1.03      | ~ v1_funct_1(X1)
% 2.19/1.03      | ~ v1_relat_1(X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_494,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.19/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.19/1.03      | ~ v1_relat_1(X1)
% 2.19/1.03      | sK6 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_495,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 2.19/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 2.19/1.03      | ~ v1_relat_1(sK6) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_494]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1092,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.19/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_496,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.19/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1934,plain,
% 2.19/1.03      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.19/1.03      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1092,c_496,c_1304,c_1433]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1935,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.19/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_1934]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2284,plain,
% 2.19/1.03      ( k2_relat_1(sK6) = k1_xboole_0
% 2.19/1.03      | r2_hidden(k4_tarski(sK1(sK6,k1_xboole_0),sK0(sK6,k1_xboole_0)),sK6) = iProver_top
% 2.19/1.03      | r2_hidden(sK1(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1843,c_1935]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_25,negated_conjecture,
% 2.19/1.03      ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
% 2.19/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_4,plain,
% 2.19/1.03      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.19/1.03      | k1_xboole_0 = X1
% 2.19/1.03      | k1_xboole_0 = X0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_91,plain,
% 2.19/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.19/1.03      | k1_xboole_0 = k1_xboole_0 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_3,plain,
% 2.19/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_92,plain,
% 2.19/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_17,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_360,plain,
% 2.19/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK6 != X2 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_361,plain,
% 2.19/1.03      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_360]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1252,plain,
% 2.19/1.03      ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
% 2.19/1.03      inference(equality_resolution,[status(thm)],[c_361]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_833,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.19/1.03      theory(equality) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1280,plain,
% 2.19/1.03      ( r2_hidden(X0,X1)
% 2.19/1.03      | ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
% 2.19/1.03      | X1 != k2_relset_1(sK3,sK4,sK6)
% 2.19/1.03      | X0 != sK5 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_833]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1289,plain,
% 2.19/1.03      ( r2_hidden(sK5,X0)
% 2.19/1.03      | ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
% 2.19/1.03      | X0 != k2_relset_1(sK3,sK4,sK6)
% 2.19/1.03      | sK5 != sK5 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_1280]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1292,plain,
% 2.19/1.03      ( ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
% 2.19/1.03      | r2_hidden(sK5,k1_xboole_0)
% 2.19/1.03      | sK5 != sK5
% 2.19/1.03      | k1_xboole_0 != k2_relset_1(sK3,sK4,sK6) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_1289]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_831,plain,( X0 = X0 ),theory(equality) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1290,plain,
% 2.19/1.03      ( sK5 = sK5 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_831]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1379,plain,
% 2.19/1.03      ( ~ r2_hidden(sK5,k1_xboole_0) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_299]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_832,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1400,plain,
% 2.19/1.03      ( X0 != X1
% 2.19/1.03      | X0 = k2_relset_1(sK3,sK4,sK6)
% 2.19/1.03      | k2_relset_1(sK3,sK4,sK6) != X1 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_832]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1910,plain,
% 2.19/1.03      ( X0 = k2_relset_1(sK3,sK4,sK6)
% 2.19/1.03      | X0 != k2_relat_1(sK6)
% 2.19/1.03      | k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_1400]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1911,plain,
% 2.19/1.03      ( k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6)
% 2.19/1.03      | k1_xboole_0 = k2_relset_1(sK3,sK4,sK6)
% 2.19/1.03      | k1_xboole_0 != k2_relat_1(sK6) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_1910]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_9,plain,
% 2.19/1.03      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.19/1.03      | r2_hidden(sK0(X0,X1),X1)
% 2.19/1.03      | ~ v1_funct_1(X0)
% 2.19/1.03      | ~ v1_relat_1(X0)
% 2.19/1.03      | k2_relat_1(X0) = X1 ),
% 2.19/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_575,plain,
% 2.19/1.03      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.19/1.03      | r2_hidden(sK0(X0,X1),X1)
% 2.19/1.03      | ~ v1_relat_1(X0)
% 2.19/1.03      | k2_relat_1(X0) = X1
% 2.19/1.03      | sK6 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_28]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_576,plain,
% 2.19/1.03      ( r2_hidden(sK1(sK6,X0),k1_relat_1(sK6))
% 2.19/1.03      | r2_hidden(sK0(sK6,X0),X0)
% 2.19/1.03      | ~ v1_relat_1(sK6)
% 2.19/1.03      | k2_relat_1(sK6) = X0 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_575]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1087,plain,
% 2.19/1.03      ( k2_relat_1(sK6) = X0
% 2.19/1.03      | r2_hidden(sK1(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | r2_hidden(sK0(sK6,X0),X0) = iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_577,plain,
% 2.19/1.03      ( k2_relat_1(sK6) = X0
% 2.19/1.03      | r2_hidden(sK1(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | r2_hidden(sK0(sK6,X0),X0) = iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2001,plain,
% 2.19/1.03      ( r2_hidden(sK0(sK6,X0),X0) = iProver_top
% 2.19/1.03      | r2_hidden(sK1(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | k2_relat_1(sK6) = X0 ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1087,c_577,c_1304,c_1433]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2002,plain,
% 2.19/1.03      ( k2_relat_1(sK6) = X0
% 2.19/1.03      | r2_hidden(sK1(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | r2_hidden(sK0(sK6,X0),X0) = iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_2001]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2011,plain,
% 2.19/1.03      ( k2_relat_1(sK6) = k1_xboole_0
% 2.19/1.03      | r2_hidden(sK1(sK6,k1_xboole_0),k1_relat_1(sK6)) = iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_2002,c_1095]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2742,plain,
% 2.19/1.03      ( X0 != X1 | X0 = k2_relat_1(sK6) | k2_relat_1(sK6) != X1 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_832]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2743,plain,
% 2.19/1.03      ( k2_relat_1(sK6) != k1_xboole_0
% 2.19/1.03      | k1_xboole_0 = k2_relat_1(sK6)
% 2.19/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_2742]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_5215,plain,
% 2.19/1.03      ( r2_hidden(k4_tarski(sK1(sK6,k1_xboole_0),sK0(sK6,k1_xboole_0)),sK6) = iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_2284,c_25,c_91,c_92,c_1252,c_1292,c_1290,c_1379,c_1911,
% 2.19/1.03                 c_2011,c_2743]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_27,negated_conjecture,
% 2.19/1.03      ( v1_funct_2(sK6,sK3,sK4) ),
% 2.19/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_23,plain,
% 2.19/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.19/1.03      | k1_xboole_0 = X2 ),
% 2.19/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_324,plain,
% 2.19/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK6 != X0
% 2.19/1.03      | k1_xboole_0 = X2 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_325,plain,
% 2.19/1.03      ( ~ v1_funct_2(sK6,X0,X1)
% 2.19/1.03      | k1_relset_1(X0,X1,sK6) = X0
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | k1_xboole_0 = X1 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_324]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_674,plain,
% 2.19/1.03      ( k1_relset_1(X0,X1,sK6) = X0
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK4 != X1
% 2.19/1.03      | sK3 != X0
% 2.19/1.03      | sK6 != sK6
% 2.19/1.03      | k1_xboole_0 = X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_325]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_675,plain,
% 2.19/1.03      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | k1_xboole_0 = sK4 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_674]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_742,plain,
% 2.19/1.03      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 2.19/1.03      inference(equality_resolution_simp,[status(thm)],[c_675]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_16,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_369,plain,
% 2.19/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK6 != X2 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_370,plain,
% 2.19/1.03      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_369]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1255,plain,
% 2.19/1.03      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 2.19/1.03      inference(equality_resolution,[status(thm)],[c_370]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1344,plain,
% 2.19/1.03      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_742,c_1255]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_12,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.19/1.03      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 2.19/1.03      | ~ v1_funct_1(X1)
% 2.19/1.03      | ~ v1_relat_1(X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_509,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.19/1.03      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 2.19/1.03      | ~ v1_relat_1(X1)
% 2.19/1.03      | sK6 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_510,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 2.19/1.03      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 2.19/1.03      | ~ v1_relat_1(sK6) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_509]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1091,plain,
% 2.19/1.03      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.19/1.03      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_511,plain,
% 2.19/1.03      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.19/1.03      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1921,plain,
% 2.19/1.03      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1091,c_511,c_1304,c_1433]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1922,plain,
% 2.19/1.03      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.19/1.03      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_1921]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1929,plain,
% 2.19/1.03      ( sK4 = k1_xboole_0
% 2.19/1.03      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.19/1.03      | r2_hidden(sK2(sK6,X0),sK3) = iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1344,c_1922]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1096,plain,
% 2.19/1.03      ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1276,plain,
% 2.19/1.03      ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_1252,c_1096]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_11,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.19/1.03      | ~ v1_funct_1(X1)
% 2.19/1.03      | ~ v1_relat_1(X1)
% 2.19/1.03      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_524,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.19/1.03      | ~ v1_relat_1(X1)
% 2.19/1.03      | k1_funct_1(X1,sK2(X1,X0)) = X0
% 2.19/1.03      | sK6 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_525,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 2.19/1.03      | ~ v1_relat_1(sK6)
% 2.19/1.03      | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_524]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1090,plain,
% 2.19/1.03      ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
% 2.19/1.03      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_526,plain,
% 2.19/1.03      ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
% 2.19/1.03      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1618,plain,
% 2.19/1.03      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 2.19/1.03      | k1_funct_1(sK6,sK2(sK6,X0)) = X0 ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1090,c_526,c_1304,c_1433]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1619,plain,
% 2.19/1.03      ( k1_funct_1(sK6,sK2(sK6,X0)) = X0
% 2.19/1.03      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_1618]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1626,plain,
% 2.19/1.03      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK5 ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1276,c_1619]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_24,negated_conjecture,
% 2.19/1.03      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK6,X0) != sK5 ),
% 2.19/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1097,plain,
% 2.19/1.03      ( k1_funct_1(sK6,X0) != sK5 | r2_hidden(X0,sK3) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2127,plain,
% 2.19/1.03      ( r2_hidden(sK2(sK6,sK5),sK3) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1626,c_1097]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2125,plain,
% 2.19/1.03      ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top
% 2.19/1.03      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1626,c_1935]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1760,plain,
% 2.19/1.03      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 2.19/1.03      | ~ r2_hidden(sK5,k2_relat_1(sK6))
% 2.19/1.03      | ~ v1_relat_1(sK6) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_510]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1761,plain,
% 2.19/1.03      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | r2_hidden(sK5,k2_relat_1(sK6)) != iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_1760]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2376,plain,
% 2.19/1.03      ( r2_hidden(k4_tarski(sK2(sK6,sK5),sK5),sK6) = iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_2125,c_1276,c_1304,c_1433,c_1761]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_15,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_relat_1(X1))
% 2.19/1.03      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.19/1.03      | ~ v1_funct_1(X1)
% 2.19/1.03      | ~ v1_relat_1(X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_479,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_relat_1(X1))
% 2.19/1.03      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.19/1.03      | ~ v1_relat_1(X1)
% 2.19/1.03      | sK6 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_480,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_relat_1(sK6))
% 2.19/1.03      | ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 2.19/1.03      | ~ v1_relat_1(sK6) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_479]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1093,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_481,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.19/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1734,plain,
% 2.19/1.03      ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 2.19/1.03      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1093,c_481,c_1304,c_1433]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1735,plain,
% 2.19/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 2.19/1.03      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_1734]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2381,plain,
% 2.19/1.03      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_2376,c_1735]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2388,plain,
% 2.19/1.03      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK6,sK5),sK3) = iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1344,c_2381]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2816,plain,
% 2.19/1.03      ( sK4 = k1_xboole_0 ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1929,c_2127,c_2388]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_19,plain,
% 2.19/1.03      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.19/1.03      | k1_xboole_0 = X1
% 2.19/1.03      | k1_xboole_0 = X0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_395,plain,
% 2.19/1.03      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK6 != X0
% 2.19/1.03      | k1_xboole_0 = X0
% 2.19/1.03      | k1_xboole_0 = X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_396,plain,
% 2.19/1.03      ( ~ v1_funct_2(sK6,X0,k1_xboole_0)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | k1_xboole_0 = X0
% 2.19/1.03      | k1_xboole_0 = sK6 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_395]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_685,plain,
% 2.19/1.03      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK4 != k1_xboole_0
% 2.19/1.03      | sK3 != X0
% 2.19/1.03      | sK6 != sK6
% 2.19/1.03      | sK6 = k1_xboole_0
% 2.19/1.03      | k1_xboole_0 = X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_396]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_686,plain,
% 2.19/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK4 != k1_xboole_0
% 2.19/1.03      | sK6 = k1_xboole_0
% 2.19/1.03      | k1_xboole_0 = sK3 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_685]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2,plain,
% 2.19/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1174,plain,
% 2.19/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k1_xboole_0)
% 2.19/1.03      | sK4 != k1_xboole_0
% 2.19/1.03      | sK3 = k1_xboole_0
% 2.19/1.03      | sK6 = k1_xboole_0 ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_686,c_2]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2819,plain,
% 2.19/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.19/1.03      | sK3 = k1_xboole_0
% 2.19/1.03      | sK6 = k1_xboole_0
% 2.19/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_2816,c_1174]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2872,plain,
% 2.19/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.19/1.03      | sK3 = k1_xboole_0
% 2.19/1.03      | sK6 = k1_xboole_0 ),
% 2.19/1.03      inference(equality_resolution_simp,[status(thm)],[c_2819]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2876,plain,
% 2.19/1.03      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 2.19/1.03      | sK3 = k1_xboole_0
% 2.19/1.03      | sK6 = k1_xboole_0 ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_2872,c_2]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2877,plain,
% 2.19/1.03      ( sK3 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 2.19/1.03      inference(equality_resolution_simp,[status(thm)],[c_2876]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_22,plain,
% 2.19/1.03      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.19/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.19/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f79]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_413,plain,
% 2.19/1.03      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.19/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK6 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_414,plain,
% 2.19/1.03      ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
% 2.19/1.03      | k1_relset_1(k1_xboole_0,X0,sK6) = k1_xboole_0
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_413]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_699,plain,
% 2.19/1.03      ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_xboole_0
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK4 != X0
% 2.19/1.03      | sK3 != k1_xboole_0
% 2.19/1.03      | sK6 != sK6 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_414]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_700,plain,
% 2.19/1.03      ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.19/1.03      | sK3 != k1_xboole_0 ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_699]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1155,plain,
% 2.19/1.03      ( k1_relset_1(k1_xboole_0,sK4,sK6) = k1_xboole_0
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k1_xboole_0)
% 2.19/1.03      | sK3 != k1_xboole_0 ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_700,c_3]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2820,plain,
% 2.19/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.19/1.03      | sK3 != k1_xboole_0 ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_2816,c_1155]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1410,plain,
% 2.19/1.03      ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_3,c_370]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2822,plain,
% 2.19/1.03      ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6)
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_2816,c_1410]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2856,plain,
% 2.19/1.03      ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6)
% 2.19/1.03      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_2822,c_2]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2857,plain,
% 2.19/1.03      ( k1_relset_1(k1_xboole_0,X0,sK6) = k1_relat_1(sK6) ),
% 2.19/1.03      inference(equality_resolution_simp,[status(thm)],[c_2856]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2864,plain,
% 2.19/1.03      ( k1_relat_1(sK6) = k1_xboole_0
% 2.19/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 2.19/1.03      | sK3 != k1_xboole_0 ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_2820,c_2857]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2868,plain,
% 2.19/1.03      ( k1_relat_1(sK6) = k1_xboole_0
% 2.19/1.03      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 2.19/1.03      | sK3 != k1_xboole_0 ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_2864,c_2]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2869,plain,
% 2.19/1.03      ( k1_relat_1(sK6) = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 2.19/1.03      inference(equality_resolution_simp,[status(thm)],[c_2868]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_3547,plain,
% 2.19/1.03      ( k1_relat_1(sK6) = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_2877,c_2869]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_4226,plain,
% 2.19/1.03      ( sK6 = k1_xboole_0 | r2_hidden(sK2(sK6,sK5),k1_xboole_0) = iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_3547,c_2381]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_4266,plain,
% 2.19/1.03      ( sK6 = k1_xboole_0 ),
% 2.19/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4226,c_1095]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_5219,plain,
% 2.19/1.03      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 2.19/1.03      inference(light_normalisation,[status(thm)],[c_5215,c_4266]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_5221,plain,
% 2.19/1.03      ( $false ),
% 2.19/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_5219,c_1095]) ).
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  ------                               Statistics
% 2.19/1.03  
% 2.19/1.03  ------ General
% 2.19/1.03  
% 2.19/1.03  abstr_ref_over_cycles:                  0
% 2.19/1.03  abstr_ref_under_cycles:                 0
% 2.19/1.03  gc_basic_clause_elim:                   0
% 2.19/1.03  forced_gc_time:                         0
% 2.19/1.03  parsing_time:                           0.008
% 2.19/1.03  unif_index_cands_time:                  0.
% 2.19/1.03  unif_index_add_time:                    0.
% 2.19/1.03  orderings_time:                         0.
% 2.19/1.03  out_proof_time:                         0.011
% 2.19/1.03  total_time:                             0.172
% 2.19/1.03  num_of_symbols:                         53
% 2.19/1.03  num_of_terms:                           3621
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing
% 2.19/1.03  
% 2.19/1.03  num_of_splits:                          0
% 2.19/1.03  num_of_split_atoms:                     0
% 2.19/1.03  num_of_reused_defs:                     0
% 2.19/1.03  num_eq_ax_congr_red:                    19
% 2.19/1.03  num_of_sem_filtered_clauses:            1
% 2.19/1.03  num_of_subtypes:                        0
% 2.19/1.03  monotx_restored_types:                  0
% 2.19/1.03  sat_num_of_epr_types:                   0
% 2.19/1.03  sat_num_of_non_cyclic_types:            0
% 2.19/1.03  sat_guarded_non_collapsed_types:        0
% 2.19/1.03  num_pure_diseq_elim:                    0
% 2.19/1.03  simp_replaced_by:                       0
% 2.19/1.03  res_preprocessed:                       126
% 2.19/1.03  prep_upred:                             0
% 2.19/1.03  prep_unflattend:                        35
% 2.19/1.03  smt_new_axioms:                         0
% 2.19/1.03  pred_elim_cands:                        2
% 2.19/1.03  pred_elim:                              4
% 2.19/1.03  pred_elim_cl:                           7
% 2.19/1.03  pred_elim_cycles:                       6
% 2.19/1.03  merged_defs:                            0
% 2.19/1.03  merged_defs_ncl:                        0
% 2.19/1.03  bin_hyper_res:                          0
% 2.19/1.03  prep_cycles:                            4
% 2.19/1.03  pred_elim_time:                         0.009
% 2.19/1.03  splitting_time:                         0.
% 2.19/1.03  sem_filter_time:                        0.
% 2.19/1.03  monotx_time:                            0.
% 2.19/1.03  subtype_inf_time:                       0.
% 2.19/1.03  
% 2.19/1.03  ------ Problem properties
% 2.19/1.03  
% 2.19/1.03  clauses:                                22
% 2.19/1.03  conjectures:                            2
% 2.19/1.03  epr:                                    1
% 2.19/1.03  horn:                                   17
% 2.19/1.03  ground:                                 4
% 2.19/1.03  unary:                                  5
% 2.19/1.03  binary:                                 4
% 2.19/1.03  lits:                                   57
% 2.19/1.03  lits_eq:                                27
% 2.19/1.03  fd_pure:                                0
% 2.19/1.03  fd_pseudo:                              0
% 2.19/1.03  fd_cond:                                4
% 2.19/1.03  fd_pseudo_cond:                         1
% 2.19/1.03  ac_symbols:                             0
% 2.19/1.03  
% 2.19/1.03  ------ Propositional Solver
% 2.19/1.03  
% 2.19/1.03  prop_solver_calls:                      29
% 2.19/1.03  prop_fast_solver_calls:                 953
% 2.19/1.03  smt_solver_calls:                       0
% 2.19/1.03  smt_fast_solver_calls:                  0
% 2.19/1.03  prop_num_of_clauses:                    1742
% 2.19/1.03  prop_preprocess_simplified:             5344
% 2.19/1.03  prop_fo_subsumed:                       21
% 2.19/1.03  prop_solver_time:                       0.
% 2.19/1.03  smt_solver_time:                        0.
% 2.19/1.03  smt_fast_solver_time:                   0.
% 2.19/1.03  prop_fast_solver_time:                  0.
% 2.19/1.03  prop_unsat_core_time:                   0.
% 2.19/1.03  
% 2.19/1.03  ------ QBF
% 2.19/1.03  
% 2.19/1.03  qbf_q_res:                              0
% 2.19/1.03  qbf_num_tautologies:                    0
% 2.19/1.03  qbf_prep_cycles:                        0
% 2.19/1.03  
% 2.19/1.03  ------ BMC1
% 2.19/1.03  
% 2.19/1.03  bmc1_current_bound:                     -1
% 2.19/1.03  bmc1_last_solved_bound:                 -1
% 2.19/1.03  bmc1_unsat_core_size:                   -1
% 2.19/1.03  bmc1_unsat_core_parents_size:           -1
% 2.19/1.03  bmc1_merge_next_fun:                    0
% 2.19/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.19/1.03  
% 2.19/1.03  ------ Instantiation
% 2.19/1.03  
% 2.19/1.03  inst_num_of_clauses:                    672
% 2.19/1.03  inst_num_in_passive:                    350
% 2.19/1.03  inst_num_in_active:                     312
% 2.19/1.03  inst_num_in_unprocessed:                10
% 2.19/1.03  inst_num_of_loops:                      410
% 2.19/1.03  inst_num_of_learning_restarts:          0
% 2.19/1.03  inst_num_moves_active_passive:          94
% 2.19/1.03  inst_lit_activity:                      0
% 2.19/1.03  inst_lit_activity_moves:                0
% 2.19/1.03  inst_num_tautologies:                   0
% 2.19/1.03  inst_num_prop_implied:                  0
% 2.19/1.03  inst_num_existing_simplified:           0
% 2.19/1.03  inst_num_eq_res_simplified:             0
% 2.19/1.03  inst_num_child_elim:                    0
% 2.19/1.03  inst_num_of_dismatching_blockings:      118
% 2.19/1.03  inst_num_of_non_proper_insts:           540
% 2.19/1.03  inst_num_of_duplicates:                 0
% 2.19/1.03  inst_inst_num_from_inst_to_res:         0
% 2.19/1.03  inst_dismatching_checking_time:         0.
% 2.19/1.03  
% 2.19/1.03  ------ Resolution
% 2.19/1.03  
% 2.19/1.03  res_num_of_clauses:                     0
% 2.19/1.03  res_num_in_passive:                     0
% 2.19/1.03  res_num_in_active:                      0
% 2.19/1.03  res_num_of_loops:                       130
% 2.19/1.03  res_forward_subset_subsumed:            60
% 2.19/1.03  res_backward_subset_subsumed:           2
% 2.19/1.03  res_forward_subsumed:                   0
% 2.19/1.03  res_backward_subsumed:                  0
% 2.19/1.03  res_forward_subsumption_resolution:     0
% 2.19/1.03  res_backward_subsumption_resolution:    0
% 2.19/1.03  res_clause_to_clause_subsumption:       594
% 2.19/1.03  res_orphan_elimination:                 0
% 2.19/1.03  res_tautology_del:                      58
% 2.19/1.03  res_num_eq_res_simplified:              1
% 2.19/1.03  res_num_sel_changes:                    0
% 2.19/1.03  res_moves_from_active_to_pass:          0
% 2.19/1.03  
% 2.19/1.03  ------ Superposition
% 2.19/1.03  
% 2.19/1.03  sup_time_total:                         0.
% 2.19/1.03  sup_time_generating:                    0.
% 2.19/1.03  sup_time_sim_full:                      0.
% 2.19/1.03  sup_time_sim_immed:                     0.
% 2.19/1.03  
% 2.19/1.03  sup_num_of_clauses:                     108
% 2.19/1.03  sup_num_in_active:                      16
% 2.19/1.03  sup_num_in_passive:                     92
% 2.19/1.03  sup_num_of_loops:                       81
% 2.19/1.03  sup_fw_superposition:                   142
% 2.19/1.03  sup_bw_superposition:                   38
% 2.19/1.03  sup_immediate_simplified:               49
% 2.19/1.03  sup_given_eliminated:                   0
% 2.19/1.03  comparisons_done:                       0
% 2.19/1.03  comparisons_avoided:                    8
% 2.19/1.03  
% 2.19/1.03  ------ Simplifications
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  sim_fw_subset_subsumed:                 24
% 2.19/1.03  sim_bw_subset_subsumed:                 4
% 2.19/1.03  sim_fw_subsumed:                        4
% 2.19/1.03  sim_bw_subsumed:                        2
% 2.19/1.03  sim_fw_subsumption_res:                 3
% 2.19/1.03  sim_bw_subsumption_res:                 0
% 2.19/1.03  sim_tautology_del:                      1
% 2.19/1.03  sim_eq_tautology_del:                   38
% 2.19/1.03  sim_eq_res_simp:                        7
% 2.19/1.03  sim_fw_demodulated:                     12
% 2.19/1.03  sim_bw_demodulated:                     63
% 2.19/1.03  sim_light_normalised:                   12
% 2.19/1.03  sim_joinable_taut:                      0
% 2.19/1.03  sim_joinable_simp:                      0
% 2.19/1.03  sim_ac_normalised:                      0
% 2.19/1.03  sim_smt_subsumption:                    0
% 2.19/1.03  
%------------------------------------------------------------------------------

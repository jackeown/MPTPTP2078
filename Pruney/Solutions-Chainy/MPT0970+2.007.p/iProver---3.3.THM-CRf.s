%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:46 EST 2020

% Result     : Theorem 15.60s
% Output     : CNFRefutation 15.60s
% Verified   : 
% Statistics : Number of formulae       :  196 (6003 expanded)
%              Number of clauses        :  122 (1973 expanded)
%              Number of leaves         :   21 (1393 expanded)
%              Depth                    :   32
%              Number of atoms          :  646 (27249 expanded)
%              Number of equality atoms :  345 (9173 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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

fof(f45,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f44,f43])).

fof(f76,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f40,f39,f38])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f74,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f15])).

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

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f77,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f83,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f4,axiom,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k2_relat_1(X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k2_relat_1(X0) = k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k2_relat_1(X0) != k1_xboole_0 )
        & ( k2_relat_1(X0) = k1_xboole_0
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_xboole_0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_928,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_931,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1328,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_931])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1718,plain,
    ( sK5 = k1_xboole_0
    | k1_relset_1(sK4,sK5,sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1328,c_35])).

cnf(c_1719,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1718])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_938,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2129,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_928,c_938])).

cnf(c_2674,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1719,c_2129])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_941,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4739,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2674,c_941])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1230,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1231,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_15913,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4739,c_34,c_36,c_1231])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_953,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15922,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_15913,c_953])).

cnf(c_16471,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK4,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15922,c_953])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_12396,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_12399,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12396])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_929,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3408,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_929,c_953])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_939,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v5_relat_1(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1828,plain,
    ( v5_relat_1(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_939])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_949,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_954,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_930,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1508,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_930])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_952,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2135,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1508,c_952])).

cnf(c_2822,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(X0)))) = sK0(sK5,k2_relat_1(X0))
    | k2_relat_1(X0) = sK5
    | v5_relat_1(X0,sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_949,c_2135])).

cnf(c_2984,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6))
    | k2_relat_1(sK6) = sK5
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1828,c_2822])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_937,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2007,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_928,c_937])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2471,plain,
    ( k2_relat_1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_2007,c_28])).

cnf(c_2987,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2984,c_36,c_1231,c_2471])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_943,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5795,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_943])).

cnf(c_24137,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5795,c_34,c_36,c_1231])).

cnf(c_24143,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3408,c_24137])).

cnf(c_1238,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v5_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1239,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v5_relat_1(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_1278,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_433,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1254,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_1418,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_1544,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(sK5,k2_relat_1(sK6))
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1545,plain,
    ( sK5 = k2_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1544])).

cnf(c_1313,plain,
    ( ~ v5_relat_1(sK6,X0)
    | r1_tarski(k2_relat_1(sK6),X0)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1566,plain,
    ( ~ v5_relat_1(sK6,sK5)
    | r1_tarski(k2_relat_1(sK6),sK5)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_1567,plain,
    ( v5_relat_1(sK6,sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1566])).

cnf(c_1861,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
    | r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1862,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1861])).

cnf(c_27450,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24143,c_31,c_36,c_28,c_1231,c_1239,c_1278,c_1418,c_1545,c_1567,c_1862])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_955,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_27456,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27450,c_955])).

cnf(c_30830,plain,
    ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27456,c_31,c_36,c_28,c_1231,c_1239,c_1278,c_1418,c_1545,c_1567])).

cnf(c_30835,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2674,c_30830])).

cnf(c_34891,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16471,c_12399,c_30835])).

cnf(c_35010,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_34891,c_928])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_935,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_36403,plain,
    ( sK6 = k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_35010,c_935])).

cnf(c_104,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_108,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_432,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1437,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_1478,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_1795,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_1796,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_445,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1308,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK6
    | X2 != sK5
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_1477,plain,
    ( v1_funct_2(X0,sK4,X1)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK6
    | X1 != sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_2661,plain,
    ( v1_funct_2(sK6,sK4,X0)
    | ~ v1_funct_2(sK6,sK4,sK5)
    | X0 != sK5
    | sK6 != sK6
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_2662,plain,
    ( X0 != sK5
    | sK6 != sK6
    | sK4 != sK4
    | v1_funct_2(sK6,sK4,X0) = iProver_top
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2661])).

cnf(c_2664,plain,
    ( sK6 != sK6
    | sK4 != sK4
    | k1_xboole_0 != sK5
    | v1_funct_2(sK6,sK4,sK5) != iProver_top
    | v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2662])).

cnf(c_37448,plain,
    ( sK4 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36403,c_35,c_104,c_108,c_1437,c_1478,c_1796,c_2664,c_12399,c_30835])).

cnf(c_37449,plain,
    ( sK6 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_37448])).

cnf(c_35003,plain,
    ( k2_relat_1(sK6) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34891,c_2471])).

cnf(c_37457,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_37449,c_35003])).

cnf(c_8,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_37477,plain,
    ( sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_37457,c_8])).

cnf(c_37478,plain,
    ( sK4 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_37477])).

cnf(c_35002,plain,
    ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_34891,c_2129])).

cnf(c_37633,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_37478,c_35002])).

cnf(c_37635,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37478,c_35010])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_932,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_38766,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_37635,c_932])).

cnf(c_1483,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_1484,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_14775,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,sK4,k1_xboole_0)
    | X0 != sK6
    | X1 != sK4
    | X2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_36389,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK6,sK4,k1_xboole_0)
    | X0 != sK4
    | X1 != k1_xboole_0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_14775])).

cnf(c_36390,plain,
    ( X0 != sK4
    | X1 != k1_xboole_0
    | sK6 != sK6
    | v1_funct_2(sK6,X0,X1) = iProver_top
    | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36389])).

cnf(c_36392,plain,
    ( sK6 != sK6
    | k1_xboole_0 != sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_36390])).

cnf(c_40047,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_38766,c_35,c_104,c_108,c_1437,c_1478,c_1484,c_1796,c_2664,c_12399,c_30835,c_36392,c_37478])).

cnf(c_61396,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_37633,c_40047])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1882,plain,
    ( ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) != k1_xboole_0
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1547,plain,
    ( k2_relat_1(sK6) != X0
    | sK5 != X0
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_1548,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | sK5 = k2_relat_1(sK6)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61396,c_30835,c_12399,c_1882,c_1548,c_1418,c_1278,c_1230,c_28,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:31:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.60/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.60/2.50  
% 15.60/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.60/2.50  
% 15.60/2.50  ------  iProver source info
% 15.60/2.50  
% 15.60/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.60/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.60/2.50  git: non_committed_changes: false
% 15.60/2.50  git: last_make_outside_of_git: false
% 15.60/2.50  
% 15.60/2.50  ------ 
% 15.60/2.50  ------ Parsing...
% 15.60/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.60/2.50  
% 15.60/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.60/2.50  
% 15.60/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.60/2.50  
% 15.60/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.60/2.50  ------ Proving...
% 15.60/2.50  ------ Problem Properties 
% 15.60/2.50  
% 15.60/2.50  
% 15.60/2.50  clauses                                 33
% 15.60/2.50  conjectures                             6
% 15.60/2.50  EPR                                     5
% 15.60/2.50  Horn                                    26
% 15.60/2.50  unary                                   7
% 15.60/2.50  binary                                  8
% 15.60/2.50  lits                                    90
% 15.60/2.50  lits eq                                 26
% 15.60/2.50  fd_pure                                 0
% 15.60/2.50  fd_pseudo                               0
% 15.60/2.50  fd_cond                                 3
% 15.60/2.50  fd_pseudo_cond                          4
% 15.60/2.50  AC symbols                              0
% 15.60/2.50  
% 15.60/2.50  ------ Input Options Time Limit: Unbounded
% 15.60/2.50  
% 15.60/2.50  
% 15.60/2.50  ------ 
% 15.60/2.50  Current options:
% 15.60/2.50  ------ 
% 15.60/2.50  
% 15.60/2.50  
% 15.60/2.50  
% 15.60/2.50  
% 15.60/2.50  ------ Proving...
% 15.60/2.50  
% 15.60/2.50  
% 15.60/2.50  % SZS status Theorem for theBenchmark.p
% 15.60/2.50  
% 15.60/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.60/2.50  
% 15.60/2.50  fof(f12,conjecture,(
% 15.60/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f13,negated_conjecture,(
% 15.60/2.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.60/2.50    inference(negated_conjecture,[],[f12])).
% 15.60/2.50  
% 15.60/2.50  fof(f26,plain,(
% 15.60/2.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.60/2.50    inference(ennf_transformation,[],[f13])).
% 15.60/2.50  
% 15.60/2.50  fof(f27,plain,(
% 15.60/2.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.60/2.50    inference(flattening,[],[f26])).
% 15.60/2.50  
% 15.60/2.50  fof(f44,plain,(
% 15.60/2.50    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 15.60/2.50    introduced(choice_axiom,[])).
% 15.60/2.50  
% 15.60/2.50  fof(f43,plain,(
% 15.60/2.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 15.60/2.50    introduced(choice_axiom,[])).
% 15.60/2.50  
% 15.60/2.50  fof(f45,plain,(
% 15.60/2.50    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 15.60/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f44,f43])).
% 15.60/2.50  
% 15.60/2.50  fof(f76,plain,(
% 15.60/2.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 15.60/2.50    inference(cnf_transformation,[],[f45])).
% 15.60/2.50  
% 15.60/2.50  fof(f11,axiom,(
% 15.60/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f24,plain,(
% 15.60/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.60/2.50    inference(ennf_transformation,[],[f11])).
% 15.60/2.50  
% 15.60/2.50  fof(f25,plain,(
% 15.60/2.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.60/2.50    inference(flattening,[],[f24])).
% 15.60/2.50  
% 15.60/2.50  fof(f42,plain,(
% 15.60/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.60/2.50    inference(nnf_transformation,[],[f25])).
% 15.60/2.50  
% 15.60/2.50  fof(f68,plain,(
% 15.60/2.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.60/2.50    inference(cnf_transformation,[],[f42])).
% 15.60/2.50  
% 15.60/2.50  fof(f75,plain,(
% 15.60/2.50    v1_funct_2(sK6,sK4,sK5)),
% 15.60/2.50    inference(cnf_transformation,[],[f45])).
% 15.60/2.50  
% 15.60/2.50  fof(f9,axiom,(
% 15.60/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f22,plain,(
% 15.60/2.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.60/2.50    inference(ennf_transformation,[],[f9])).
% 15.60/2.50  
% 15.60/2.50  fof(f66,plain,(
% 15.60/2.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.60/2.50    inference(cnf_transformation,[],[f22])).
% 15.60/2.50  
% 15.60/2.50  fof(f6,axiom,(
% 15.60/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f18,plain,(
% 15.60/2.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.60/2.50    inference(ennf_transformation,[],[f6])).
% 15.60/2.50  
% 15.60/2.50  fof(f19,plain,(
% 15.60/2.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.60/2.50    inference(flattening,[],[f18])).
% 15.60/2.50  
% 15.60/2.50  fof(f36,plain,(
% 15.60/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.60/2.50    inference(nnf_transformation,[],[f19])).
% 15.60/2.50  
% 15.60/2.50  fof(f37,plain,(
% 15.60/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.60/2.50    inference(rectify,[],[f36])).
% 15.60/2.50  
% 15.60/2.50  fof(f40,plain,(
% 15.60/2.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 15.60/2.50    introduced(choice_axiom,[])).
% 15.60/2.50  
% 15.60/2.50  fof(f39,plain,(
% 15.60/2.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 15.60/2.50    introduced(choice_axiom,[])).
% 15.60/2.50  
% 15.60/2.50  fof(f38,plain,(
% 15.60/2.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 15.60/2.50    introduced(choice_axiom,[])).
% 15.60/2.50  
% 15.60/2.50  fof(f41,plain,(
% 15.60/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.60/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f40,f39,f38])).
% 15.60/2.50  
% 15.60/2.50  fof(f58,plain,(
% 15.60/2.50    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f41])).
% 15.60/2.50  
% 15.60/2.50  fof(f85,plain,(
% 15.60/2.50    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.60/2.50    inference(equality_resolution,[],[f58])).
% 15.60/2.50  
% 15.60/2.50  fof(f74,plain,(
% 15.60/2.50    v1_funct_1(sK6)),
% 15.60/2.50    inference(cnf_transformation,[],[f45])).
% 15.60/2.50  
% 15.60/2.50  fof(f7,axiom,(
% 15.60/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f20,plain,(
% 15.60/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.60/2.50    inference(ennf_transformation,[],[f7])).
% 15.60/2.50  
% 15.60/2.50  fof(f64,plain,(
% 15.60/2.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.60/2.50    inference(cnf_transformation,[],[f20])).
% 15.60/2.50  
% 15.60/2.50  fof(f1,axiom,(
% 15.60/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f15,plain,(
% 15.60/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.60/2.50    inference(ennf_transformation,[],[f1])).
% 15.60/2.50  
% 15.60/2.50  fof(f28,plain,(
% 15.60/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.60/2.50    inference(nnf_transformation,[],[f15])).
% 15.60/2.50  
% 15.60/2.50  fof(f29,plain,(
% 15.60/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.60/2.50    inference(rectify,[],[f28])).
% 15.60/2.50  
% 15.60/2.50  fof(f30,plain,(
% 15.60/2.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.60/2.50    introduced(choice_axiom,[])).
% 15.60/2.50  
% 15.60/2.50  fof(f31,plain,(
% 15.60/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.60/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 15.60/2.50  
% 15.60/2.50  fof(f46,plain,(
% 15.60/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f31])).
% 15.60/2.50  
% 15.60/2.50  fof(f2,axiom,(
% 15.60/2.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f32,plain,(
% 15.60/2.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.60/2.50    inference(nnf_transformation,[],[f2])).
% 15.60/2.50  
% 15.60/2.50  fof(f33,plain,(
% 15.60/2.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.60/2.50    inference(flattening,[],[f32])).
% 15.60/2.50  
% 15.60/2.50  fof(f49,plain,(
% 15.60/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.60/2.50    inference(cnf_transformation,[],[f33])).
% 15.60/2.50  
% 15.60/2.50  fof(f81,plain,(
% 15.60/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.60/2.50    inference(equality_resolution,[],[f49])).
% 15.60/2.50  
% 15.60/2.50  fof(f77,plain,(
% 15.60/2.50    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f45])).
% 15.60/2.50  
% 15.60/2.50  fof(f8,axiom,(
% 15.60/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f14,plain,(
% 15.60/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 15.60/2.50    inference(pure_predicate_removal,[],[f8])).
% 15.60/2.50  
% 15.60/2.50  fof(f21,plain,(
% 15.60/2.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.60/2.50    inference(ennf_transformation,[],[f14])).
% 15.60/2.50  
% 15.60/2.50  fof(f65,plain,(
% 15.60/2.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.60/2.50    inference(cnf_transformation,[],[f21])).
% 15.60/2.50  
% 15.60/2.50  fof(f3,axiom,(
% 15.60/2.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f16,plain,(
% 15.60/2.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.60/2.50    inference(ennf_transformation,[],[f3])).
% 15.60/2.50  
% 15.60/2.50  fof(f34,plain,(
% 15.60/2.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.60/2.50    inference(nnf_transformation,[],[f16])).
% 15.60/2.50  
% 15.60/2.50  fof(f52,plain,(
% 15.60/2.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f34])).
% 15.60/2.50  
% 15.60/2.50  fof(f47,plain,(
% 15.60/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f31])).
% 15.60/2.50  
% 15.60/2.50  fof(f78,plain,(
% 15.60/2.50    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f45])).
% 15.60/2.50  
% 15.60/2.50  fof(f51,plain,(
% 15.60/2.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f33])).
% 15.60/2.50  
% 15.60/2.50  fof(f10,axiom,(
% 15.60/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f23,plain,(
% 15.60/2.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.60/2.50    inference(ennf_transformation,[],[f10])).
% 15.60/2.50  
% 15.60/2.50  fof(f67,plain,(
% 15.60/2.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.60/2.50    inference(cnf_transformation,[],[f23])).
% 15.60/2.50  
% 15.60/2.50  fof(f79,plain,(
% 15.60/2.50    k2_relset_1(sK4,sK5,sK6) != sK5),
% 15.60/2.50    inference(cnf_transformation,[],[f45])).
% 15.60/2.50  
% 15.60/2.50  fof(f60,plain,(
% 15.60/2.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f41])).
% 15.60/2.50  
% 15.60/2.50  fof(f82,plain,(
% 15.60/2.50    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.60/2.50    inference(equality_resolution,[],[f60])).
% 15.60/2.50  
% 15.60/2.50  fof(f83,plain,(
% 15.60/2.50    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.60/2.50    inference(equality_resolution,[],[f82])).
% 15.60/2.50  
% 15.60/2.50  fof(f48,plain,(
% 15.60/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f31])).
% 15.60/2.50  
% 15.60/2.50  fof(f72,plain,(
% 15.60/2.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.60/2.50    inference(cnf_transformation,[],[f42])).
% 15.60/2.50  
% 15.60/2.50  fof(f88,plain,(
% 15.60/2.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 15.60/2.50    inference(equality_resolution,[],[f72])).
% 15.60/2.50  
% 15.60/2.50  fof(f4,axiom,(
% 15.60/2.50    k2_relat_1(k1_xboole_0) = k1_xboole_0 & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f55,plain,(
% 15.60/2.50    k2_relat_1(k1_xboole_0) = k1_xboole_0),
% 15.60/2.50    inference(cnf_transformation,[],[f4])).
% 15.60/2.50  
% 15.60/2.50  fof(f69,plain,(
% 15.60/2.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.60/2.50    inference(cnf_transformation,[],[f42])).
% 15.60/2.50  
% 15.60/2.50  fof(f90,plain,(
% 15.60/2.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 15.60/2.50    inference(equality_resolution,[],[f69])).
% 15.60/2.50  
% 15.60/2.50  fof(f5,axiom,(
% 15.60/2.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k2_relat_1(X0) = k1_xboole_0))),
% 15.60/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.50  
% 15.60/2.50  fof(f17,plain,(
% 15.60/2.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k2_relat_1(X0) = k1_xboole_0) | ~v1_relat_1(X0))),
% 15.60/2.50    inference(ennf_transformation,[],[f5])).
% 15.60/2.50  
% 15.60/2.50  fof(f35,plain,(
% 15.60/2.50    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0) & (k2_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 15.60/2.50    inference(nnf_transformation,[],[f17])).
% 15.60/2.50  
% 15.60/2.50  fof(f56,plain,(
% 15.60/2.50    ( ! [X0] : (k2_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 15.60/2.50    inference(cnf_transformation,[],[f35])).
% 15.60/2.50  
% 15.60/2.50  cnf(c_31,negated_conjecture,
% 15.60/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 15.60/2.50      inference(cnf_transformation,[],[f76]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_928,plain,
% 15.60/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_27,plain,
% 15.60/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.60/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.60/2.50      | k1_relset_1(X1,X2,X0) = X1
% 15.60/2.50      | k1_xboole_0 = X2 ),
% 15.60/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_931,plain,
% 15.60/2.50      ( k1_relset_1(X0,X1,X2) = X0
% 15.60/2.50      | k1_xboole_0 = X1
% 15.60/2.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.60/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1328,plain,
% 15.60/2.50      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 15.60/2.50      | sK5 = k1_xboole_0
% 15.60/2.50      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_928,c_931]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_32,negated_conjecture,
% 15.60/2.50      ( v1_funct_2(sK6,sK4,sK5) ),
% 15.60/2.50      inference(cnf_transformation,[],[f75]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_35,plain,
% 15.60/2.50      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1718,plain,
% 15.60/2.50      ( sK5 = k1_xboole_0 | k1_relset_1(sK4,sK5,sK6) = sK4 ),
% 15.60/2.50      inference(global_propositional_subsumption,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_1328,c_35]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1719,plain,
% 15.60/2.50      ( k1_relset_1(sK4,sK5,sK6) = sK4 | sK5 = k1_xboole_0 ),
% 15.60/2.50      inference(renaming,[status(thm)],[c_1718]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_20,plain,
% 15.60/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.60/2.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.60/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_938,plain,
% 15.60/2.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.60/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2129,plain,
% 15.60/2.50      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_928,c_938]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2674,plain,
% 15.60/2.50      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_1719,c_2129]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_17,plain,
% 15.60/2.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.60/2.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 15.60/2.50      | ~ v1_funct_1(X1)
% 15.60/2.50      | ~ v1_relat_1(X1) ),
% 15.60/2.50      inference(cnf_transformation,[],[f85]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_941,plain,
% 15.60/2.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 15.60/2.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 15.60/2.50      | v1_funct_1(X1) != iProver_top
% 15.60/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_4739,plain,
% 15.60/2.50      ( sK5 = k1_xboole_0
% 15.60/2.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.60/2.50      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
% 15.60/2.50      | v1_funct_1(sK6) != iProver_top
% 15.60/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_2674,c_941]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_33,negated_conjecture,
% 15.60/2.50      ( v1_funct_1(sK6) ),
% 15.60/2.50      inference(cnf_transformation,[],[f74]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_34,plain,
% 15.60/2.50      ( v1_funct_1(sK6) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_36,plain,
% 15.60/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_18,plain,
% 15.60/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.60/2.50      | v1_relat_1(X0) ),
% 15.60/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1230,plain,
% 15.60/2.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 15.60/2.50      | v1_relat_1(sK6) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_18]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1231,plain,
% 15.60/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 15.60/2.50      | v1_relat_1(sK6) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_15913,plain,
% 15.60/2.50      ( sK5 = k1_xboole_0
% 15.60/2.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.60/2.50      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top ),
% 15.60/2.50      inference(global_propositional_subsumption,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_4739,c_34,c_36,c_1231]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2,plain,
% 15.60/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.60/2.50      inference(cnf_transformation,[],[f46]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_953,plain,
% 15.60/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.60/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.60/2.50      | r1_tarski(X1,X2) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_15922,plain,
% 15.60/2.50      ( sK5 = k1_xboole_0
% 15.60/2.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.60/2.50      | r2_hidden(sK3(sK6,X0),X1) = iProver_top
% 15.60/2.50      | r1_tarski(sK4,X1) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_15913,c_953]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_16471,plain,
% 15.60/2.50      ( sK5 = k1_xboole_0
% 15.60/2.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.60/2.50      | r2_hidden(sK3(sK6,X0),X1) = iProver_top
% 15.60/2.50      | r1_tarski(X2,X1) != iProver_top
% 15.60/2.50      | r1_tarski(sK4,X2) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_15922,c_953]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_5,plain,
% 15.60/2.50      ( r1_tarski(X0,X0) ),
% 15.60/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_12396,plain,
% 15.60/2.50      ( r1_tarski(sK4,sK4) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_5]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_12399,plain,
% 15.60/2.50      ( r1_tarski(sK4,sK4) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_12396]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_30,negated_conjecture,
% 15.60/2.50      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 15.60/2.50      inference(cnf_transformation,[],[f77]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_929,plain,
% 15.60/2.50      ( r2_hidden(X0,sK5) != iProver_top
% 15.60/2.50      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_3408,plain,
% 15.60/2.50      ( r2_hidden(X0,sK5) != iProver_top
% 15.60/2.50      | r2_hidden(sK7(X0),X1) = iProver_top
% 15.60/2.50      | r1_tarski(sK4,X1) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_929,c_953]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_19,plain,
% 15.60/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.60/2.50      | v5_relat_1(X0,X2) ),
% 15.60/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_939,plain,
% 15.60/2.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.60/2.50      | v5_relat_1(X0,X2) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1828,plain,
% 15.60/2.50      ( v5_relat_1(sK6,sK5) = iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_928,c_939]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_7,plain,
% 15.60/2.50      ( ~ v5_relat_1(X0,X1)
% 15.60/2.50      | r1_tarski(k2_relat_1(X0),X1)
% 15.60/2.50      | ~ v1_relat_1(X0) ),
% 15.60/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_949,plain,
% 15.60/2.50      ( v5_relat_1(X0,X1) != iProver_top
% 15.60/2.50      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 15.60/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1,plain,
% 15.60/2.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.60/2.50      inference(cnf_transformation,[],[f47]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_954,plain,
% 15.60/2.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.60/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_29,negated_conjecture,
% 15.60/2.50      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 15.60/2.50      inference(cnf_transformation,[],[f78]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_930,plain,
% 15.60/2.50      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1508,plain,
% 15.60/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 15.60/2.50      | r1_tarski(sK5,X0) = iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_954,c_930]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_3,plain,
% 15.60/2.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 15.60/2.50      inference(cnf_transformation,[],[f51]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_952,plain,
% 15.60/2.50      ( X0 = X1
% 15.60/2.50      | r1_tarski(X1,X0) != iProver_top
% 15.60/2.50      | r1_tarski(X0,X1) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2135,plain,
% 15.60/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 15.60/2.50      | sK5 = X0
% 15.60/2.50      | r1_tarski(X0,sK5) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_1508,c_952]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2822,plain,
% 15.60/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(X0)))) = sK0(sK5,k2_relat_1(X0))
% 15.60/2.50      | k2_relat_1(X0) = sK5
% 15.60/2.50      | v5_relat_1(X0,sK5) != iProver_top
% 15.60/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_949,c_2135]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2984,plain,
% 15.60/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6))
% 15.60/2.50      | k2_relat_1(sK6) = sK5
% 15.60/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_1828,c_2822]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_21,plain,
% 15.60/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.60/2.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.60/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_937,plain,
% 15.60/2.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.60/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2007,plain,
% 15.60/2.50      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_928,c_937]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_28,negated_conjecture,
% 15.60/2.50      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 15.60/2.50      inference(cnf_transformation,[],[f79]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2471,plain,
% 15.60/2.50      ( k2_relat_1(sK6) != sK5 ),
% 15.60/2.50      inference(demodulation,[status(thm)],[c_2007,c_28]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2987,plain,
% 15.60/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
% 15.60/2.50      inference(global_propositional_subsumption,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_2984,c_36,c_1231,c_2471]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_15,plain,
% 15.60/2.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.60/2.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 15.60/2.50      | ~ v1_funct_1(X1)
% 15.60/2.50      | ~ v1_relat_1(X1) ),
% 15.60/2.50      inference(cnf_transformation,[],[f83]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_943,plain,
% 15.60/2.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 15.60/2.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 15.60/2.50      | v1_funct_1(X1) != iProver_top
% 15.60/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_5795,plain,
% 15.60/2.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 15.60/2.50      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top
% 15.60/2.50      | v1_funct_1(sK6) != iProver_top
% 15.60/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_2987,c_943]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_24137,plain,
% 15.60/2.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 15.60/2.50      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
% 15.60/2.50      inference(global_propositional_subsumption,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_5795,c_34,c_36,c_1231]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_24143,plain,
% 15.60/2.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 15.60/2.50      | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
% 15.60/2.50      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_3408,c_24137]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1238,plain,
% 15.60/2.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 15.60/2.50      | v5_relat_1(sK6,sK5) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_19]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1239,plain,
% 15.60/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 15.60/2.50      | v5_relat_1(sK6,sK5) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1278,plain,
% 15.60/2.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 15.60/2.50      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_21]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_433,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1254,plain,
% 15.60/2.50      ( k2_relset_1(sK4,sK5,sK6) != X0
% 15.60/2.50      | k2_relset_1(sK4,sK5,sK6) = sK5
% 15.60/2.50      | sK5 != X0 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_433]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1418,plain,
% 15.60/2.50      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 15.60/2.50      | k2_relset_1(sK4,sK5,sK6) = sK5
% 15.60/2.50      | sK5 != k2_relat_1(sK6) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_1254]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1544,plain,
% 15.60/2.50      ( ~ r1_tarski(k2_relat_1(sK6),sK5)
% 15.60/2.50      | ~ r1_tarski(sK5,k2_relat_1(sK6))
% 15.60/2.50      | sK5 = k2_relat_1(sK6) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1545,plain,
% 15.60/2.50      ( sK5 = k2_relat_1(sK6)
% 15.60/2.50      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
% 15.60/2.50      | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_1544]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1313,plain,
% 15.60/2.50      ( ~ v5_relat_1(sK6,X0)
% 15.60/2.50      | r1_tarski(k2_relat_1(sK6),X0)
% 15.60/2.50      | ~ v1_relat_1(sK6) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_7]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1566,plain,
% 15.60/2.50      ( ~ v5_relat_1(sK6,sK5)
% 15.60/2.50      | r1_tarski(k2_relat_1(sK6),sK5)
% 15.60/2.50      | ~ v1_relat_1(sK6) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_1313]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1567,plain,
% 15.60/2.50      ( v5_relat_1(sK6,sK5) != iProver_top
% 15.60/2.50      | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
% 15.60/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_1566]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1861,plain,
% 15.60/2.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
% 15.60/2.50      | r1_tarski(sK5,k2_relat_1(sK6)) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_1]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1862,plain,
% 15.60/2.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
% 15.60/2.50      | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_1861]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_27450,plain,
% 15.60/2.50      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 15.60/2.50      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 15.60/2.50      inference(global_propositional_subsumption,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_24143,c_31,c_36,c_28,c_1231,c_1239,c_1278,c_1418,
% 15.60/2.50                 c_1545,c_1567,c_1862]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_0,plain,
% 15.60/2.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.60/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_955,plain,
% 15.60/2.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.60/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_27456,plain,
% 15.60/2.50      ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
% 15.60/2.50      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_27450,c_955]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_30830,plain,
% 15.60/2.50      ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 15.60/2.50      inference(global_propositional_subsumption,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_27456,c_31,c_36,c_28,c_1231,c_1239,c_1278,c_1418,
% 15.60/2.50                 c_1545,c_1567]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_30835,plain,
% 15.60/2.50      ( sK5 = k1_xboole_0 | r1_tarski(sK4,sK4) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_2674,c_30830]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_34891,plain,
% 15.60/2.50      ( sK5 = k1_xboole_0 ),
% 15.60/2.50      inference(global_propositional_subsumption,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_16471,c_12399,c_30835]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_35010,plain,
% 15.60/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 15.60/2.50      inference(demodulation,[status(thm)],[c_34891,c_928]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_23,plain,
% 15.60/2.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 15.60/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 15.60/2.50      | k1_xboole_0 = X1
% 15.60/2.50      | k1_xboole_0 = X0 ),
% 15.60/2.50      inference(cnf_transformation,[],[f88]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_935,plain,
% 15.60/2.50      ( k1_xboole_0 = X0
% 15.60/2.50      | k1_xboole_0 = X1
% 15.60/2.50      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 15.60/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_36403,plain,
% 15.60/2.50      ( sK6 = k1_xboole_0
% 15.60/2.50      | sK4 = k1_xboole_0
% 15.60/2.50      | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_35010,c_935]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_104,plain,
% 15.60/2.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_5]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_108,plain,
% 15.60/2.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.60/2.50      | k1_xboole_0 = k1_xboole_0 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_432,plain,( X0 = X0 ),theory(equality) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1437,plain,
% 15.60/2.50      ( sK6 = sK6 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_432]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1478,plain,
% 15.60/2.50      ( sK4 = sK4 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_432]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1795,plain,
% 15.60/2.50      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_433]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1796,plain,
% 15.60/2.50      ( sK5 != k1_xboole_0
% 15.60/2.50      | k1_xboole_0 = sK5
% 15.60/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_1795]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_445,plain,
% 15.60/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.60/2.50      | v1_funct_2(X3,X4,X5)
% 15.60/2.50      | X3 != X0
% 15.60/2.50      | X4 != X1
% 15.60/2.50      | X5 != X2 ),
% 15.60/2.50      theory(equality) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1308,plain,
% 15.60/2.50      ( v1_funct_2(X0,X1,X2)
% 15.60/2.50      | ~ v1_funct_2(sK6,sK4,sK5)
% 15.60/2.50      | X0 != sK6
% 15.60/2.50      | X2 != sK5
% 15.60/2.50      | X1 != sK4 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_445]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1477,plain,
% 15.60/2.50      ( v1_funct_2(X0,sK4,X1)
% 15.60/2.50      | ~ v1_funct_2(sK6,sK4,sK5)
% 15.60/2.50      | X0 != sK6
% 15.60/2.50      | X1 != sK5
% 15.60/2.50      | sK4 != sK4 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_1308]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2661,plain,
% 15.60/2.50      ( v1_funct_2(sK6,sK4,X0)
% 15.60/2.50      | ~ v1_funct_2(sK6,sK4,sK5)
% 15.60/2.50      | X0 != sK5
% 15.60/2.50      | sK6 != sK6
% 15.60/2.50      | sK4 != sK4 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_1477]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2662,plain,
% 15.60/2.50      ( X0 != sK5
% 15.60/2.50      | sK6 != sK6
% 15.60/2.50      | sK4 != sK4
% 15.60/2.50      | v1_funct_2(sK6,sK4,X0) = iProver_top
% 15.60/2.50      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_2661]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_2664,plain,
% 15.60/2.50      ( sK6 != sK6
% 15.60/2.50      | sK4 != sK4
% 15.60/2.50      | k1_xboole_0 != sK5
% 15.60/2.50      | v1_funct_2(sK6,sK4,sK5) != iProver_top
% 15.60/2.50      | v1_funct_2(sK6,sK4,k1_xboole_0) = iProver_top ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_2662]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_37448,plain,
% 15.60/2.50      ( sK4 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 15.60/2.50      inference(global_propositional_subsumption,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_36403,c_35,c_104,c_108,c_1437,c_1478,c_1796,c_2664,
% 15.60/2.50                 c_12399,c_30835]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_37449,plain,
% 15.60/2.50      ( sK6 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 15.60/2.50      inference(renaming,[status(thm)],[c_37448]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_35003,plain,
% 15.60/2.50      ( k2_relat_1(sK6) != k1_xboole_0 ),
% 15.60/2.50      inference(demodulation,[status(thm)],[c_34891,c_2471]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_37457,plain,
% 15.60/2.50      ( k2_relat_1(k1_xboole_0) != k1_xboole_0 | sK4 = k1_xboole_0 ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_37449,c_35003]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_8,plain,
% 15.60/2.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.60/2.50      inference(cnf_transformation,[],[f55]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_37477,plain,
% 15.60/2.50      ( sK4 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 15.60/2.50      inference(light_normalisation,[status(thm)],[c_37457,c_8]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_37478,plain,
% 15.60/2.50      ( sK4 = k1_xboole_0 ),
% 15.60/2.50      inference(equality_resolution_simp,[status(thm)],[c_37477]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_35002,plain,
% 15.60/2.50      ( k1_relset_1(sK4,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 15.60/2.50      inference(demodulation,[status(thm)],[c_34891,c_2129]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_37633,plain,
% 15.60/2.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 15.60/2.50      inference(demodulation,[status(thm)],[c_37478,c_35002]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_37635,plain,
% 15.60/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 15.60/2.50      inference(demodulation,[status(thm)],[c_37478,c_35010]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_26,plain,
% 15.60/2.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 15.60/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.60/2.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 15.60/2.50      inference(cnf_transformation,[],[f90]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_932,plain,
% 15.60/2.50      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 15.60/2.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 15.60/2.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_38766,plain,
% 15.60/2.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 15.60/2.50      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.60/2.50      inference(superposition,[status(thm)],[c_37635,c_932]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1483,plain,
% 15.60/2.50      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_433]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1484,plain,
% 15.60/2.50      ( sK4 != k1_xboole_0
% 15.60/2.50      | k1_xboole_0 = sK4
% 15.60/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_1483]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_14775,plain,
% 15.60/2.50      ( v1_funct_2(X0,X1,X2)
% 15.60/2.50      | ~ v1_funct_2(sK6,sK4,k1_xboole_0)
% 15.60/2.50      | X0 != sK6
% 15.60/2.50      | X1 != sK4
% 15.60/2.50      | X2 != k1_xboole_0 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_445]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_36389,plain,
% 15.60/2.50      ( v1_funct_2(sK6,X0,X1)
% 15.60/2.50      | ~ v1_funct_2(sK6,sK4,k1_xboole_0)
% 15.60/2.50      | X0 != sK4
% 15.60/2.50      | X1 != k1_xboole_0
% 15.60/2.50      | sK6 != sK6 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_14775]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_36390,plain,
% 15.60/2.50      ( X0 != sK4
% 15.60/2.50      | X1 != k1_xboole_0
% 15.60/2.50      | sK6 != sK6
% 15.60/2.50      | v1_funct_2(sK6,X0,X1) = iProver_top
% 15.60/2.50      | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top ),
% 15.60/2.50      inference(predicate_to_equality,[status(thm)],[c_36389]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_36392,plain,
% 15.60/2.50      ( sK6 != sK6
% 15.60/2.50      | k1_xboole_0 != sK4
% 15.60/2.50      | k1_xboole_0 != k1_xboole_0
% 15.60/2.50      | v1_funct_2(sK6,sK4,k1_xboole_0) != iProver_top
% 15.60/2.50      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_36390]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_40047,plain,
% 15.60/2.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 15.60/2.50      inference(global_propositional_subsumption,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_38766,c_35,c_104,c_108,c_1437,c_1478,c_1484,c_1796,
% 15.60/2.50                 c_2664,c_12399,c_30835,c_36392,c_37478]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_61396,plain,
% 15.60/2.50      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 15.60/2.50      inference(light_normalisation,[status(thm)],[c_37633,c_40047]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_11,plain,
% 15.60/2.50      ( ~ v1_relat_1(X0)
% 15.60/2.50      | k1_relat_1(X0) != k1_xboole_0
% 15.60/2.50      | k2_relat_1(X0) = k1_xboole_0 ),
% 15.60/2.50      inference(cnf_transformation,[],[f56]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1882,plain,
% 15.60/2.50      ( ~ v1_relat_1(sK6)
% 15.60/2.50      | k1_relat_1(sK6) != k1_xboole_0
% 15.60/2.50      | k2_relat_1(sK6) = k1_xboole_0 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_11]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1547,plain,
% 15.60/2.50      ( k2_relat_1(sK6) != X0 | sK5 != X0 | sK5 = k2_relat_1(sK6) ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_433]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(c_1548,plain,
% 15.60/2.50      ( k2_relat_1(sK6) != k1_xboole_0
% 15.60/2.50      | sK5 = k2_relat_1(sK6)
% 15.60/2.50      | sK5 != k1_xboole_0 ),
% 15.60/2.50      inference(instantiation,[status(thm)],[c_1547]) ).
% 15.60/2.50  
% 15.60/2.50  cnf(contradiction,plain,
% 15.60/2.50      ( $false ),
% 15.60/2.50      inference(minisat,
% 15.60/2.50                [status(thm)],
% 15.60/2.50                [c_61396,c_30835,c_12399,c_1882,c_1548,c_1418,c_1278,
% 15.60/2.50                 c_1230,c_28,c_31]) ).
% 15.60/2.50  
% 15.60/2.50  
% 15.60/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.60/2.50  
% 15.60/2.50  ------                               Statistics
% 15.60/2.50  
% 15.60/2.50  ------ Selected
% 15.60/2.50  
% 15.60/2.50  total_time:                             1.729
% 15.60/2.50  
%------------------------------------------------------------------------------

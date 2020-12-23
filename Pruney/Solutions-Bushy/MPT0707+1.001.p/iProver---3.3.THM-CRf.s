%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0707+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:57 EST 2020

% Result     : Theorem 27.43s
% Output     : CNFRefutation 27.43s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 494 expanded)
%              Number of clauses        :  134 ( 215 expanded)
%              Number of leaves         :   17 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          :  686 (2261 expanded)
%              Number of equality atoms :  333 ( 876 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1)
            & r2_hidden(sK3(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23,f22,f21])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k9_relat_1(k6_relat_1(sK4),sK5) != sK5
      & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k9_relat_1(k6_relat_1(sK4),sK5) != sK5
    & m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f18,f30])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f50,plain,(
    k9_relat_1(k6_relat_1(sK4),sK5) != sK5 ),
    inference(cnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,X4) != sK0(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_606,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2893,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)),X2)
    | X1 != X2
    | X0 != k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_90117,plain,
    ( r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),X0)
    | ~ r2_hidden(k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)),X1)
    | X0 != X1
    | sK0(k6_relat_1(sK4),sK5,sK5) != k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_2893])).

cnf(c_90118,plain,
    ( X0 != X1
    | sK0(k6_relat_1(sK4),sK5,sK5) != k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5))
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),X0) = iProver_top
    | r2_hidden(k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_90117])).

cnf(c_90120,plain,
    ( sK0(k6_relat_1(sK4),sK5,sK5) != k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5))
    | sK5 != sK5
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) = iProver_top
    | r2_hidden(k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_90118])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15926,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(k6_relat_1(sK4)))
    | r2_hidden(X0,k1_relat_1(k6_relat_1(sK4)))
    | v1_xboole_0(k1_relat_1(k6_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_45214,plain,
    ( ~ m1_subset_1(sK0(k6_relat_1(sK4),sK5,X0),k1_relat_1(k6_relat_1(sK4)))
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,X0),k1_relat_1(k6_relat_1(sK4)))
    | v1_xboole_0(k1_relat_1(k6_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_15926])).

cnf(c_45215,plain,
    ( m1_subset_1(sK0(k6_relat_1(sK4),sK5,X0),k1_relat_1(k6_relat_1(sK4))) != iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,X0),k1_relat_1(k6_relat_1(sK4))) = iProver_top
    | v1_xboole_0(k1_relat_1(k6_relat_1(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45214])).

cnf(c_45217,plain,
    ( m1_subset_1(sK0(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4))) != iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4))) = iProver_top
    | v1_xboole_0(k1_relat_1(k6_relat_1(sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45215])).

cnf(c_602,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_15762,plain,
    ( sK0(k6_relat_1(X0),sK5,X1) != X2
    | sK0(k6_relat_1(X0),sK5,X1) = k1_funct_1(k6_relat_1(X0),sK0(k6_relat_1(sK4),sK5,sK5))
    | k1_funct_1(k6_relat_1(X0),sK0(k6_relat_1(sK4),sK5,sK5)) != X2 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_41305,plain,
    ( sK0(k6_relat_1(sK4),sK5,X0) != sK0(k6_relat_1(sK4),sK5,sK5)
    | sK0(k6_relat_1(sK4),sK5,X0) = k1_funct_1(k6_relat_1(sK4),sK0(k6_relat_1(sK4),sK5,sK5))
    | k1_funct_1(k6_relat_1(sK4),sK0(k6_relat_1(sK4),sK5,sK5)) != sK0(k6_relat_1(sK4),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_15762])).

cnf(c_41306,plain,
    ( sK0(k6_relat_1(sK4),sK5,sK5) != sK0(k6_relat_1(sK4),sK5,sK5)
    | sK0(k6_relat_1(sK4),sK5,sK5) = k1_funct_1(k6_relat_1(sK4),sK0(k6_relat_1(sK4),sK5,sK5))
    | k1_funct_1(k6_relat_1(sK4),sK0(k6_relat_1(sK4),sK5,sK5)) != sK0(k6_relat_1(sK4),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_41305])).

cnf(c_8344,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),X2)
    | X1 != X2
    | X0 != sK1(k6_relat_1(sK4),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_28073,plain,
    ( ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),X0)
    | r2_hidden(k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,X1)),sK5)
    | k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,X1)) != sK1(k6_relat_1(sK4),sK5,sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_8344])).

cnf(c_38605,plain,
    ( ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(X0)))
    | r2_hidden(k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,X1)),sK5)
    | k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,X1)) != sK1(k6_relat_1(sK4),sK5,sK5)
    | sK5 != k1_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_28073])).

cnf(c_38606,plain,
    ( k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,X0)) != sK1(k6_relat_1(sK4),sK5,sK5)
    | sK5 != k1_relat_1(k6_relat_1(X1))
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(X1))) != iProver_top
    | r2_hidden(k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,X0)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38605])).

cnf(c_38608,plain,
    ( k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) != sK1(k6_relat_1(sK4),sK5,sK5)
    | sK5 != k1_relat_1(k6_relat_1(sK5))
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK5))) != iProver_top
    | r2_hidden(k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_38606])).

cnf(c_1650,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4)))
    | X0 != sK1(k6_relat_1(sK4),sK5,sK5)
    | X1 != k1_relat_1(k6_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_21208,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4)))
    | X0 != sK1(k6_relat_1(sK4),sK5,sK5)
    | sK4 != k1_relat_1(k6_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_37014,plain,
    ( ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4)))
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK4)
    | sK1(k6_relat_1(sK4),sK5,sK5) != sK1(k6_relat_1(sK4),sK5,sK5)
    | sK4 != k1_relat_1(k6_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_21208])).

cnf(c_37020,plain,
    ( sK1(k6_relat_1(sK4),sK5,sK5) != sK1(k6_relat_1(sK4),sK5,sK5)
    | sK4 != k1_relat_1(k6_relat_1(sK4))
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4))) != iProver_top
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37014])).

cnf(c_19174,plain,
    ( X0 != X1
    | X0 = k1_relat_1(k6_relat_1(X2))
    | k1_relat_1(k6_relat_1(X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_19175,plain,
    ( k1_relat_1(k6_relat_1(sK5)) != sK5
    | sK5 = k1_relat_1(k6_relat_1(sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_19174])).

cnf(c_1918,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_4046,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_10390,plain,
    ( k1_relat_1(k6_relat_1(sK4)) != sK4
    | sK4 = k1_relat_1(k6_relat_1(sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4046])).

cnf(c_6389,plain,
    ( sK0(k6_relat_1(sK4),sK5,X0) != X1
    | sK0(k6_relat_1(sK4),sK5,X0) = k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5))
    | k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) != X1 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_10126,plain,
    ( sK0(k6_relat_1(sK4),sK5,X0) != sK0(k6_relat_1(sK4),sK5,sK5)
    | sK0(k6_relat_1(sK4),sK5,X0) = k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5))
    | k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) != sK0(k6_relat_1(sK4),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_6389])).

cnf(c_10127,plain,
    ( sK0(k6_relat_1(sK4),sK5,sK5) != sK0(k6_relat_1(sK4),sK5,sK5)
    | sK0(k6_relat_1(sK4),sK5,sK5) = k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5))
    | k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) != sK0(k6_relat_1(sK4),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_10126])).

cnf(c_1067,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5)
    | X0 != sK1(k6_relat_1(sK4),sK5,sK5)
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_1752,plain,
    ( r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),X0)
    | ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5)
    | X0 != sK5
    | sK1(k6_relat_1(sK4),sK5,sK5) != sK1(k6_relat_1(sK4),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1067])).

cnf(c_8387,plain,
    ( r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(X0)))
    | ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5)
    | sK1(k6_relat_1(sK4),sK5,sK5) != sK1(k6_relat_1(sK4),sK5,sK5)
    | k1_relat_1(k6_relat_1(X0)) != sK5 ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_8388,plain,
    ( sK1(k6_relat_1(sK4),sK5,sK5) != sK1(k6_relat_1(sK4),sK5,sK5)
    | k1_relat_1(k6_relat_1(X0)) != sK5
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(X0))) = iProver_top
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8387])).

cnf(c_8390,plain,
    ( sK1(k6_relat_1(sK4),sK5,sK5) != sK1(k6_relat_1(sK4),sK5,sK5)
    | k1_relat_1(k6_relat_1(sK5)) != sK5
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK5))) = iProver_top
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8388])).

cnf(c_8,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(k6_relat_1(X1))
    | ~ v1_funct_1(k6_relat_1(X1))
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_420,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(k6_relat_1(X1))
    | k1_funct_1(k6_relat_1(X1),X0) = X0
    | k6_relat_1(X1) != k6_relat_1(X2) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_432,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k6_relat_1(X1),X0) = X0
    | k6_relat_1(X1) != k6_relat_1(X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_420,c_9])).

cnf(c_5787,plain,
    ( ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK4)
    | k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) = sK1(k6_relat_1(sK4),sK5,sK5)
    | k6_relat_1(sK4) != k6_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_8263,plain,
    ( ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK4)
    | k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) = sK1(k6_relat_1(sK4),sK5,sK5)
    | k6_relat_1(sK4) != k6_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5787])).

cnf(c_8264,plain,
    ( k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) = sK1(k6_relat_1(sK4),sK5,sK5)
    | k6_relat_1(sK4) != k6_relat_1(sK4)
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8263])).

cnf(c_2989,plain,
    ( ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK4)
    | k1_funct_1(k6_relat_1(sK4),sK0(k6_relat_1(sK4),sK5,sK5)) = sK0(k6_relat_1(sK4),sK5,sK5)
    | k6_relat_1(sK4) != k6_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_8256,plain,
    ( ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK4)
    | k1_funct_1(k6_relat_1(sK4),sK0(k6_relat_1(sK4),sK5,sK5)) = sK0(k6_relat_1(sK4),sK5,sK5)
    | k6_relat_1(sK4) != k6_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2989])).

cnf(c_8257,plain,
    ( k1_funct_1(k6_relat_1(sK4),sK0(k6_relat_1(sK4),sK5,sK5)) = sK0(k6_relat_1(sK4),sK5,sK5)
    | k6_relat_1(sK4) != k6_relat_1(sK4)
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8256])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_260,plain,
    ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2
    | k6_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_261,plain,
    ( r2_hidden(sK1(k6_relat_1(X0),X1,X2),k1_relat_1(k6_relat_1(X0)))
    | r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2)
    | ~ v1_relat_1(k6_relat_1(X0))
    | k9_relat_1(k6_relat_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_265,plain,
    ( r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2)
    | r2_hidden(sK1(k6_relat_1(X0),X1,X2),k1_relat_1(k6_relat_1(X0)))
    | k9_relat_1(k6_relat_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_9])).

cnf(c_266,plain,
    ( r2_hidden(sK1(k6_relat_1(X0),X1,X2),k1_relat_1(k6_relat_1(X0)))
    | r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2)
    | k9_relat_1(k6_relat_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_865,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X2
    | r2_hidden(sK1(k6_relat_1(X0),X1,X2),k1_relat_1(k6_relat_1(X0))) = iProver_top
    | r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_14,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | ~ v1_funct_1(k6_relat_1(X0))
    | k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_111,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_9,c_8])).

cnf(c_929,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X2
    | r2_hidden(sK1(k6_relat_1(X0),X1,X2),X0) = iProver_top
    | r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_865,c_111])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_867,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_868,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1203,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_867,c_868])).

cnf(c_2195,plain,
    ( k9_relat_1(k6_relat_1(sK5),X0) = X1
    | r2_hidden(sK0(k6_relat_1(sK5),X0,X1),X1) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_929,c_1203])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k6_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_370,plain,
    ( ~ r2_hidden(X0,k9_relat_1(k6_relat_1(X1),X2))
    | r2_hidden(sK2(k6_relat_1(X1),X2,X0),k1_relat_1(k6_relat_1(X1)))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_380,plain,
    ( ~ r2_hidden(X0,k9_relat_1(k6_relat_1(X1),X2))
    | r2_hidden(sK2(k6_relat_1(X1),X2,X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_370,c_9])).

cnf(c_860,plain,
    ( r2_hidden(X0,k9_relat_1(k6_relat_1(X1),X2)) != iProver_top
    | r2_hidden(sK2(k6_relat_1(X1),X2,X0),k1_relat_1(k6_relat_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_910,plain,
    ( r2_hidden(X0,k9_relat_1(k6_relat_1(X1),X2)) != iProver_top
    | r2_hidden(sK2(k6_relat_1(X1),X2,X0),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_860,c_111])).

cnf(c_1378,plain,
    ( r2_hidden(X0,k9_relat_1(k6_relat_1(sK5),X1)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_1203])).

cnf(c_1632,plain,
    ( r2_hidden(X0,k9_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(sK5),X1)),X2)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_1378])).

cnf(c_5213,plain,
    ( k9_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(sK5),X0)),X1) = k9_relat_1(k6_relat_1(sK5),X2)
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_1632])).

cnf(c_19,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( k9_relat_1(k6_relat_1(sK4),sK5) != sK5 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_281,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2
    | k6_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_282,plain,
    ( r2_hidden(sK1(k6_relat_1(X0),X1,X2),X1)
    | r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2)
    | ~ v1_relat_1(k6_relat_1(X0))
    | k9_relat_1(k6_relat_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_286,plain,
    ( r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2)
    | r2_hidden(sK1(k6_relat_1(X0),X1,X2),X1)
    | k9_relat_1(k6_relat_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_9])).

cnf(c_287,plain,
    ( r2_hidden(sK1(k6_relat_1(X0),X1,X2),X1)
    | r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2)
    | k9_relat_1(k6_relat_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_286])).

cnf(c_1010,plain,
    ( r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5)
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5)
    | k9_relat_1(k6_relat_1(sK4),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_1011,plain,
    ( k9_relat_1(k6_relat_1(sK4),sK5) = sK5
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5) = iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(c_3200,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6791,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3200])).

cnf(c_6792,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6791])).

cnf(c_5726,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6806,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5726])).

cnf(c_6807,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),sK5) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6806])).

cnf(c_6869,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5213,c_19,c_17,c_1011,c_6792,c_6807])).

cnf(c_6800,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4))))
    | ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5)
    | ~ v1_xboole_0(k1_relat_1(k6_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_3200])).

cnf(c_6801,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4)))) != iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) != iProver_top
    | v1_xboole_0(k1_relat_1(k6_relat_1(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6800])).

cnf(c_601,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4047,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(k6_relat_1(sK4),sK5,X0),X1)
    | ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,X0),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3964,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4))))
    | m1_subset_1(sK0(k6_relat_1(sK4),sK5,X0),k1_relat_1(k6_relat_1(sK4)))
    | ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,X0),X0) ),
    inference(instantiation,[status(thm)],[c_1418])).

cnf(c_3965,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4)))) != iProver_top
    | m1_subset_1(sK0(k6_relat_1(sK4),sK5,X0),k1_relat_1(k6_relat_1(sK4))) = iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3964])).

cnf(c_3967,plain,
    ( m1_subset_1(sK0(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4)))) != iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3965])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_997,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | X1 != k1_zfmisc_1(sK4)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_1128,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | X0 != sK5
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_1906,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | X0 != sK5
    | k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4))) != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_1907,plain,
    ( X0 != sK5
    | k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4))) != k1_zfmisc_1(sK4)
    | m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1906])).

cnf(c_1909,plain,
    ( k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4))) != k1_zfmisc_1(sK4)
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1907])).

cnf(c_1753,plain,
    ( sK1(k6_relat_1(sK4),sK5,sK5) = sK1(k6_relat_1(sK4),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_1529,plain,
    ( ~ m1_subset_1(sK0(k6_relat_1(sK4),sK5,sK5),sK4)
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1530,plain,
    ( m1_subset_1(sK0(k6_relat_1(sK4),sK5,sK5),sK4) != iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1529])).

cnf(c_1403,plain,
    ( k6_relat_1(sK4) = k6_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_1317,plain,
    ( sK0(k6_relat_1(sK4),sK5,sK5) = sK0(k6_relat_1(sK4),sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_1261,plain,
    ( k1_relat_1(k6_relat_1(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_613,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1129,plain,
    ( X0 != sK4
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_1260,plain,
    ( k1_zfmisc_1(k1_relat_1(k6_relat_1(sK4))) = k1_zfmisc_1(sK4)
    | k1_relat_1(k6_relat_1(sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_1062,plain,
    ( m1_subset_1(sK0(k6_relat_1(sK4),sK5,sK5),X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1214,plain,
    ( m1_subset_1(sK0(k6_relat_1(sK4),sK5,sK5),sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_1215,plain,
    ( m1_subset_1(sK0(k6_relat_1(sK4),sK5,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK4)) != iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1214])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | sK0(X2,X1,X3) != k1_funct_1(X2,X0)
    | k9_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_343,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | ~ r2_hidden(sK0(X2,X1,X3),X3)
    | ~ v1_relat_1(X2)
    | sK0(X2,X1,X3) != k1_funct_1(X2,X0)
    | k9_relat_1(X2,X1) = X3
    | k6_relat_1(X4) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(X2)))
    | ~ r2_hidden(sK0(k6_relat_1(X2),X1,X3),X3)
    | ~ v1_relat_1(k6_relat_1(X2))
    | sK0(k6_relat_1(X2),X1,X3) != k1_funct_1(k6_relat_1(X2),X0)
    | k9_relat_1(k6_relat_1(X2),X1) = X3 ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_360,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k6_relat_1(X2)))
    | ~ r2_hidden(sK0(k6_relat_1(X2),X1,X3),X3)
    | sK0(k6_relat_1(X2),X1,X3) != k1_funct_1(k6_relat_1(X2),X0)
    | k9_relat_1(k6_relat_1(X2),X1) = X3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_344,c_9])).

cnf(c_1002,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k6_relat_1(sK4)))
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5)
    | sK0(k6_relat_1(sK4),sK5,sK5) != k1_funct_1(k6_relat_1(sK4),X0)
    | k9_relat_1(k6_relat_1(sK4),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_1110,plain,
    ( ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4)))
    | ~ r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5)
    | sK0(k6_relat_1(sK4),sK5,sK5) != k1_funct_1(k6_relat_1(sK4),sK0(k6_relat_1(sK4),sK5,sK5))
    | k9_relat_1(k6_relat_1(sK4),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_1111,plain,
    ( sK0(k6_relat_1(sK4),sK5,sK5) != k1_funct_1(k6_relat_1(sK4),sK0(k6_relat_1(sK4),sK5,sK5))
    | k9_relat_1(k6_relat_1(sK4),sK5) = sK5
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4))) != iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_302,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
    | k9_relat_1(X0,X1) = X2
    | k6_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_303,plain,
    ( r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2)
    | ~ v1_relat_1(k6_relat_1(X0))
    | k1_funct_1(k6_relat_1(X0),sK1(k6_relat_1(X0),X1,X2)) = sK0(k6_relat_1(X0),X1,X2)
    | k9_relat_1(k6_relat_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_307,plain,
    ( r2_hidden(sK0(k6_relat_1(X0),X1,X2),X2)
    | k1_funct_1(k6_relat_1(X0),sK1(k6_relat_1(X0),X1,X2)) = sK0(k6_relat_1(X0),X1,X2)
    | k9_relat_1(k6_relat_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_9])).

cnf(c_1013,plain,
    ( r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5)
    | k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) = sK0(k6_relat_1(sK4),sK5,sK5)
    | k9_relat_1(k6_relat_1(sK4),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_1014,plain,
    ( k1_funct_1(k6_relat_1(sK4),sK1(k6_relat_1(sK4),sK5,sK5)) = sK0(k6_relat_1(sK4),sK5,sK5)
    | k9_relat_1(k6_relat_1(sK4),sK5) = sK5
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_1007,plain,
    ( r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4)))
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5)
    | k9_relat_1(k6_relat_1(sK4),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_1008,plain,
    ( k9_relat_1(k6_relat_1(sK4),sK5) = sK5
    | r2_hidden(sK1(k6_relat_1(sK4),sK5,sK5),k1_relat_1(k6_relat_1(sK4))) = iProver_top
    | r2_hidden(sK0(k6_relat_1(sK4),sK5,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_626,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_45,plain,
    ( v1_funct_1(k6_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_42,plain,
    ( v1_relat_1(k6_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_27,plain,
    ( ~ v1_relat_1(k6_relat_1(sK5))
    | ~ v1_funct_1(k6_relat_1(sK5))
    | k1_relat_1(k6_relat_1(sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_90120,c_45217,c_41306,c_38608,c_37020,c_19175,c_10390,c_10127,c_8390,c_8264,c_8257,c_6869,c_6801,c_4047,c_3967,c_1909,c_1753,c_1530,c_1403,c_1317,c_1261,c_1260,c_1215,c_1111,c_1014,c_1011,c_1008,c_626,c_45,c_42,c_27,c_17,c_19])).


%------------------------------------------------------------------------------

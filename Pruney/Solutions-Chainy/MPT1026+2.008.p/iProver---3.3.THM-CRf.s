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
% DateTime   : Thu Dec  3 12:08:13 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.07s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 839 expanded)
%              Number of clauses        :  103 ( 301 expanded)
%              Number of leaves         :   28 ( 213 expanded)
%              Depth                    :   19
%              Number of atoms          :  712 (5046 expanded)
%              Number of equality atoms :  229 (1490 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
        | ~ v1_funct_2(sK13,sK11,sK12)
        | ~ v1_funct_1(sK13) )
      & r2_hidden(sK13,k1_funct_2(sK11,sK12)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
      | ~ v1_funct_2(sK13,sK11,sK12)
      | ~ v1_funct_1(sK13) )
    & r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f22,f50])).

fof(f88,plain,(
    r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f9,f23])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f99,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f83])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X0)
                  | k1_relat_1(X4) != X1
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X0)
                  & k1_relat_1(X5) = X1
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X0)
                  & k1_relat_1(X8) = X1
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X0)
        & k1_relat_1(sK10(X0,X1,X6)) = X1
        & sK10(X0,X1,X6) = X6
        & v1_funct_1(sK10(X0,X1,X6))
        & v1_relat_1(sK10(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X0)
        & k1_relat_1(sK9(X0,X1,X2)) = X1
        & sK9(X0,X1,X2) = X3
        & v1_funct_1(sK9(X0,X1,X2))
        & v1_relat_1(sK9(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X0)
                & k1_relat_1(X5) = X1
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X0)
              | k1_relat_1(X4) != X1
              | sK8(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK8(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK8(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X0)
              & k1_relat_1(sK9(X0,X1,X2)) = X1
              & sK8(X0,X1,X2) = sK9(X0,X1,X2)
              & v1_funct_1(sK9(X0,X1,X2))
              & v1_relat_1(sK9(X0,X1,X2)) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X0)
                & k1_relat_1(sK10(X0,X1,X6)) = X1
                & sK10(X0,X1,X6) = X6
                & v1_funct_1(sK10(X0,X1,X6))
                & v1_relat_1(sK10(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f44,f47,f46,f45])).

fof(f74,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK10(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    ! [X6,X2,X0,X1] :
      ( sK10(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK10(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK10(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f38,f41,f40,f39])).

fof(f62,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5137,plain,
    ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5139,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK10(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5144,plain,
    ( k1_relat_1(sK10(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7023,plain,
    ( k1_relat_1(sK10(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5139,c_5144])).

cnf(c_12850,plain,
    ( k1_relat_1(sK10(sK12,sK11,sK13)) = sK11 ),
    inference(superposition,[status(thm)],[c_5137,c_7023])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK10(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5143,plain,
    ( sK10(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6591,plain,
    ( sK10(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5139,c_5143])).

cnf(c_7824,plain,
    ( sK10(sK12,sK11,sK13) = sK13 ),
    inference(superposition,[status(thm)],[c_5137,c_6591])).

cnf(c_12852,plain,
    ( k1_relat_1(sK13) = sK11 ),
    inference(light_normalisation,[status(thm)],[c_12850,c_7824])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_552,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_553,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_557,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_33])).

cnf(c_14,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36,negated_conjecture,
    ( ~ v1_funct_2(sK13,sK11,sK12)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_576,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK13)
    | sK12 != X2
    | sK11 != X1
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_577,plain,
    ( ~ v1_partfun1(sK13,sK11)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_641,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK11
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_557,c_577])).

cnf(c_642,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(sK13)
    | v1_xboole_0(k2_relat_1(sK13))
    | k1_relat_1(sK13) != sK11 ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_5133,plain,
    ( k1_relat_1(sK13) != sK11
    | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_13723,plain,
    ( sK11 != sK11
    | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12852,c_5133])).

cnf(c_13734,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13723])).

cnf(c_38,plain,
    ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_128,plain,
    ( r1_tarski(sK13,sK13) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_132,plain,
    ( ~ r1_tarski(sK13,sK13)
    | sK13 = sK13 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_643,plain,
    ( k1_relat_1(sK13) != sK11
    | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK10(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5442,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | v1_funct_1(sK10(X0,X1,sK13)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_5536,plain,
    ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | v1_funct_1(sK10(sK12,sK11,sK13)) ),
    inference(instantiation,[status(thm)],[c_5442])).

cnf(c_5538,plain,
    ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
    | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top
    | v1_funct_1(sK10(sK12,sK11,sK13)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5536])).

cnf(c_5537,plain,
    ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_5540,plain,
    ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5537])).

cnf(c_4542,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5672,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK10(sK12,sK11,sK13))
    | X0 != sK10(sK12,sK11,sK13) ),
    inference(instantiation,[status(thm)],[c_4542])).

cnf(c_5673,plain,
    ( X0 != sK10(sK12,sK11,sK13)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK10(sK12,sK11,sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5672])).

cnf(c_5675,plain,
    ( sK13 != sK10(sK12,sK11,sK13)
    | v1_funct_1(sK10(sK12,sK11,sK13)) != iProver_top
    | v1_funct_1(sK13) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5673])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK10(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5447,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | v1_relat_1(sK10(X0,X1,sK13)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_5690,plain,
    ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | v1_relat_1(sK10(sK12,sK11,sK13)) ),
    inference(instantiation,[status(thm)],[c_5447])).

cnf(c_5692,plain,
    ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
    | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top
    | v1_relat_1(sK10(sK12,sK11,sK13)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5690])).

cnf(c_5482,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | sK10(X0,X1,sK13) = sK13 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_5688,plain,
    ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | sK10(sK12,sK11,sK13) = sK13 ),
    inference(instantiation,[status(thm)],[c_5482])).

cnf(c_4541,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5810,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK10(sK12,sK11,sK13))
    | X0 != sK10(sK12,sK11,sK13) ),
    inference(instantiation,[status(thm)],[c_4541])).

cnf(c_5816,plain,
    ( X0 != sK10(sK12,sK11,sK13)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK10(sK12,sK11,sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5810])).

cnf(c_5818,plain,
    ( sK13 != sK10(sK12,sK11,sK13)
    | v1_relat_1(sK10(sK12,sK11,sK13)) != iProver_top
    | v1_relat_1(sK13) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5816])).

cnf(c_4531,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6107,plain,
    ( X0 != X1
    | X0 = sK10(sK12,sK11,sK13)
    | sK10(sK12,sK11,sK13) != X1 ),
    inference(instantiation,[status(thm)],[c_4531])).

cnf(c_6108,plain,
    ( sK10(sK12,sK11,sK13) != sK13
    | sK13 = sK10(sK12,sK11,sK13)
    | sK13 != sK13 ),
    inference(instantiation,[status(thm)],[c_6107])).

cnf(c_21269,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13734,c_37,c_38,c_128,c_132,c_643,c_5538,c_5537,c_5540,c_5675,c_5692,c_5688,c_5818,c_6108,c_12852])).

cnf(c_21275,plain,
    ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
    | r1_tarski(k1_relat_1(sK13),sK11) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5153,c_21269])).

cnf(c_21276,plain,
    ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
    | r1_tarski(sK11,sK11) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21275,c_12852])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK10(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5466,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
    | r1_tarski(k2_relat_1(sK10(X0,X1,sK13)),X0)
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_5689,plain,
    ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
    | r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12)
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_5466])).

cnf(c_5694,plain,
    ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
    | r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12) = iProver_top
    | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5689])).

cnf(c_4534,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_7432,plain,
    ( ~ r1_tarski(X0,sK12)
    | r1_tarski(X1,sK12)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_4534])).

cnf(c_13705,plain,
    ( r1_tarski(X0,sK12)
    | ~ r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12)
    | X0 != k2_relat_1(sK10(sK12,sK11,sK13)) ),
    inference(instantiation,[status(thm)],[c_7432])).

cnf(c_15730,plain,
    ( r1_tarski(k2_relat_1(X0),sK12)
    | ~ r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12)
    | k2_relat_1(X0) != k2_relat_1(sK10(sK12,sK11,sK13)) ),
    inference(instantiation,[status(thm)],[c_13705])).

cnf(c_15732,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK10(sK12,sK11,sK13))
    | r1_tarski(k2_relat_1(X0),sK12) = iProver_top
    | r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15730])).

cnf(c_15734,plain,
    ( k2_relat_1(sK13) != k2_relat_1(sK10(sK12,sK11,sK13))
    | r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12) != iProver_top
    | r1_tarski(k2_relat_1(sK13),sK12) = iProver_top ),
    inference(instantiation,[status(thm)],[c_15732])).

cnf(c_4537,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_15731,plain,
    ( X0 != sK10(sK12,sK11,sK13)
    | k2_relat_1(X0) = k2_relat_1(sK10(sK12,sK11,sK13)) ),
    inference(instantiation,[status(thm)],[c_4537])).

cnf(c_15736,plain,
    ( k2_relat_1(sK13) = k2_relat_1(sK10(sK12,sK11,sK13))
    | sK13 != sK10(sK12,sK11,sK13) ),
    inference(instantiation,[status(thm)],[c_15731])).

cnf(c_18612,plain,
    ( r1_tarski(sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_18615,plain,
    ( r1_tarski(sK11,sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18612])).

cnf(c_21540,plain,
    ( v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21276,c_37,c_38,c_128,c_132,c_5537,c_5540,c_5692,c_5694,c_5688,c_5818,c_6108,c_15734,c_15736,c_18615])).

cnf(c_0,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5165,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_5158,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_5155,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6497,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),k2_relat_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5158,c_5155])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5164,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11539,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6497,c_5164])).

cnf(c_11653,plain,
    ( v1_xboole_0(k2_relat_1(X0)) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5165,c_11539])).

cnf(c_21545,plain,
    ( v1_xboole_0(k1_relat_1(sK13)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21540,c_11653])).

cnf(c_21556,plain,
    ( v1_xboole_0(sK11) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21545,c_12852])).

cnf(c_16,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13)
    | ~ v1_xboole_0(X1)
    | sK11 != X1
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_577])).

cnf(c_624,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0)))
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13)
    | ~ v1_xboole_0(sK11) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_4528,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13)
    | ~ v1_xboole_0(sK11)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_624])).

cnf(c_5134,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_xboole_0(sK11) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4528])).

cnf(c_4527,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_624])).

cnf(c_5135,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4527])).

cnf(c_5292,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5134,c_5135])).

cnf(c_10038,plain,
    ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
    | r1_tarski(k1_relat_1(sK13),sK11) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_5153,c_5292])).

cnf(c_10413,plain,
    ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
    | r1_tarski(k1_relat_1(sK13),sK11) != iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10038,c_37,c_38,c_128,c_132,c_5538,c_5537,c_5540,c_5675,c_5692,c_5688,c_5818,c_6108])).

cnf(c_13721,plain,
    ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
    | r1_tarski(sK11,sK11) != iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12852,c_10413])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21556,c_18615,c_15736,c_15734,c_13721,c_6108,c_5688,c_5694,c_5540,c_5537,c_132,c_128,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.07/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.07/1.49  
% 7.07/1.49  ------  iProver source info
% 7.07/1.49  
% 7.07/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.07/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.07/1.49  git: non_committed_changes: false
% 7.07/1.49  git: last_make_outside_of_git: false
% 7.07/1.49  
% 7.07/1.49  ------ 
% 7.07/1.49  
% 7.07/1.49  ------ Input Options
% 7.07/1.49  
% 7.07/1.49  --out_options                           all
% 7.07/1.49  --tptp_safe_out                         true
% 7.07/1.49  --problem_path                          ""
% 7.07/1.49  --include_path                          ""
% 7.07/1.49  --clausifier                            res/vclausify_rel
% 7.07/1.49  --clausifier_options                    --mode clausify
% 7.07/1.49  --stdin                                 false
% 7.07/1.49  --stats_out                             all
% 7.07/1.49  
% 7.07/1.49  ------ General Options
% 7.07/1.49  
% 7.07/1.49  --fof                                   false
% 7.07/1.49  --time_out_real                         305.
% 7.07/1.49  --time_out_virtual                      -1.
% 7.07/1.49  --symbol_type_check                     false
% 7.07/1.49  --clausify_out                          false
% 7.07/1.49  --sig_cnt_out                           false
% 7.07/1.49  --trig_cnt_out                          false
% 7.07/1.49  --trig_cnt_out_tolerance                1.
% 7.07/1.49  --trig_cnt_out_sk_spl                   false
% 7.07/1.49  --abstr_cl_out                          false
% 7.07/1.49  
% 7.07/1.49  ------ Global Options
% 7.07/1.49  
% 7.07/1.49  --schedule                              default
% 7.07/1.49  --add_important_lit                     false
% 7.07/1.49  --prop_solver_per_cl                    1000
% 7.07/1.49  --min_unsat_core                        false
% 7.07/1.49  --soft_assumptions                      false
% 7.07/1.49  --soft_lemma_size                       3
% 7.07/1.49  --prop_impl_unit_size                   0
% 7.07/1.49  --prop_impl_unit                        []
% 7.07/1.49  --share_sel_clauses                     true
% 7.07/1.49  --reset_solvers                         false
% 7.07/1.49  --bc_imp_inh                            [conj_cone]
% 7.07/1.49  --conj_cone_tolerance                   3.
% 7.07/1.49  --extra_neg_conj                        none
% 7.07/1.49  --large_theory_mode                     true
% 7.07/1.49  --prolific_symb_bound                   200
% 7.07/1.49  --lt_threshold                          2000
% 7.07/1.49  --clause_weak_htbl                      true
% 7.07/1.49  --gc_record_bc_elim                     false
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing Options
% 7.07/1.49  
% 7.07/1.49  --preprocessing_flag                    true
% 7.07/1.49  --time_out_prep_mult                    0.1
% 7.07/1.49  --splitting_mode                        input
% 7.07/1.49  --splitting_grd                         true
% 7.07/1.49  --splitting_cvd                         false
% 7.07/1.49  --splitting_cvd_svl                     false
% 7.07/1.49  --splitting_nvd                         32
% 7.07/1.49  --sub_typing                            true
% 7.07/1.49  --prep_gs_sim                           true
% 7.07/1.49  --prep_unflatten                        true
% 7.07/1.49  --prep_res_sim                          true
% 7.07/1.49  --prep_upred                            true
% 7.07/1.49  --prep_sem_filter                       exhaustive
% 7.07/1.49  --prep_sem_filter_out                   false
% 7.07/1.49  --pred_elim                             true
% 7.07/1.49  --res_sim_input                         true
% 7.07/1.49  --eq_ax_congr_red                       true
% 7.07/1.49  --pure_diseq_elim                       true
% 7.07/1.49  --brand_transform                       false
% 7.07/1.49  --non_eq_to_eq                          false
% 7.07/1.49  --prep_def_merge                        true
% 7.07/1.49  --prep_def_merge_prop_impl              false
% 7.07/1.49  --prep_def_merge_mbd                    true
% 7.07/1.49  --prep_def_merge_tr_red                 false
% 7.07/1.49  --prep_def_merge_tr_cl                  false
% 7.07/1.49  --smt_preprocessing                     true
% 7.07/1.49  --smt_ac_axioms                         fast
% 7.07/1.49  --preprocessed_out                      false
% 7.07/1.49  --preprocessed_stats                    false
% 7.07/1.49  
% 7.07/1.49  ------ Abstraction refinement Options
% 7.07/1.49  
% 7.07/1.49  --abstr_ref                             []
% 7.07/1.49  --abstr_ref_prep                        false
% 7.07/1.49  --abstr_ref_until_sat                   false
% 7.07/1.49  --abstr_ref_sig_restrict                funpre
% 7.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.07/1.49  --abstr_ref_under                       []
% 7.07/1.49  
% 7.07/1.49  ------ SAT Options
% 7.07/1.49  
% 7.07/1.49  --sat_mode                              false
% 7.07/1.49  --sat_fm_restart_options                ""
% 7.07/1.49  --sat_gr_def                            false
% 7.07/1.49  --sat_epr_types                         true
% 7.07/1.49  --sat_non_cyclic_types                  false
% 7.07/1.49  --sat_finite_models                     false
% 7.07/1.49  --sat_fm_lemmas                         false
% 7.07/1.49  --sat_fm_prep                           false
% 7.07/1.49  --sat_fm_uc_incr                        true
% 7.07/1.49  --sat_out_model                         small
% 7.07/1.49  --sat_out_clauses                       false
% 7.07/1.49  
% 7.07/1.49  ------ QBF Options
% 7.07/1.49  
% 7.07/1.49  --qbf_mode                              false
% 7.07/1.49  --qbf_elim_univ                         false
% 7.07/1.49  --qbf_dom_inst                          none
% 7.07/1.49  --qbf_dom_pre_inst                      false
% 7.07/1.49  --qbf_sk_in                             false
% 7.07/1.49  --qbf_pred_elim                         true
% 7.07/1.49  --qbf_split                             512
% 7.07/1.49  
% 7.07/1.49  ------ BMC1 Options
% 7.07/1.49  
% 7.07/1.49  --bmc1_incremental                      false
% 7.07/1.49  --bmc1_axioms                           reachable_all
% 7.07/1.49  --bmc1_min_bound                        0
% 7.07/1.49  --bmc1_max_bound                        -1
% 7.07/1.49  --bmc1_max_bound_default                -1
% 7.07/1.49  --bmc1_symbol_reachability              true
% 7.07/1.49  --bmc1_property_lemmas                  false
% 7.07/1.49  --bmc1_k_induction                      false
% 7.07/1.49  --bmc1_non_equiv_states                 false
% 7.07/1.49  --bmc1_deadlock                         false
% 7.07/1.49  --bmc1_ucm                              false
% 7.07/1.49  --bmc1_add_unsat_core                   none
% 7.07/1.49  --bmc1_unsat_core_children              false
% 7.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.07/1.49  --bmc1_out_stat                         full
% 7.07/1.49  --bmc1_ground_init                      false
% 7.07/1.49  --bmc1_pre_inst_next_state              false
% 7.07/1.49  --bmc1_pre_inst_state                   false
% 7.07/1.49  --bmc1_pre_inst_reach_state             false
% 7.07/1.49  --bmc1_out_unsat_core                   false
% 7.07/1.49  --bmc1_aig_witness_out                  false
% 7.07/1.49  --bmc1_verbose                          false
% 7.07/1.49  --bmc1_dump_clauses_tptp                false
% 7.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.07/1.49  --bmc1_dump_file                        -
% 7.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.07/1.49  --bmc1_ucm_extend_mode                  1
% 7.07/1.49  --bmc1_ucm_init_mode                    2
% 7.07/1.49  --bmc1_ucm_cone_mode                    none
% 7.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.07/1.49  --bmc1_ucm_relax_model                  4
% 7.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.07/1.49  --bmc1_ucm_layered_model                none
% 7.07/1.49  --bmc1_ucm_max_lemma_size               10
% 7.07/1.49  
% 7.07/1.49  ------ AIG Options
% 7.07/1.49  
% 7.07/1.49  --aig_mode                              false
% 7.07/1.49  
% 7.07/1.49  ------ Instantiation Options
% 7.07/1.49  
% 7.07/1.49  --instantiation_flag                    true
% 7.07/1.49  --inst_sos_flag                         false
% 7.07/1.49  --inst_sos_phase                        true
% 7.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel_side                     num_symb
% 7.07/1.49  --inst_solver_per_active                1400
% 7.07/1.49  --inst_solver_calls_frac                1.
% 7.07/1.49  --inst_passive_queue_type               priority_queues
% 7.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.07/1.49  --inst_passive_queues_freq              [25;2]
% 7.07/1.49  --inst_dismatching                      true
% 7.07/1.49  --inst_eager_unprocessed_to_passive     true
% 7.07/1.49  --inst_prop_sim_given                   true
% 7.07/1.49  --inst_prop_sim_new                     false
% 7.07/1.49  --inst_subs_new                         false
% 7.07/1.49  --inst_eq_res_simp                      false
% 7.07/1.49  --inst_subs_given                       false
% 7.07/1.49  --inst_orphan_elimination               true
% 7.07/1.49  --inst_learning_loop_flag               true
% 7.07/1.49  --inst_learning_start                   3000
% 7.07/1.49  --inst_learning_factor                  2
% 7.07/1.49  --inst_start_prop_sim_after_learn       3
% 7.07/1.49  --inst_sel_renew                        solver
% 7.07/1.49  --inst_lit_activity_flag                true
% 7.07/1.49  --inst_restr_to_given                   false
% 7.07/1.49  --inst_activity_threshold               500
% 7.07/1.49  --inst_out_proof                        true
% 7.07/1.49  
% 7.07/1.49  ------ Resolution Options
% 7.07/1.49  
% 7.07/1.49  --resolution_flag                       true
% 7.07/1.49  --res_lit_sel                           adaptive
% 7.07/1.49  --res_lit_sel_side                      none
% 7.07/1.49  --res_ordering                          kbo
% 7.07/1.49  --res_to_prop_solver                    active
% 7.07/1.49  --res_prop_simpl_new                    false
% 7.07/1.49  --res_prop_simpl_given                  true
% 7.07/1.49  --res_passive_queue_type                priority_queues
% 7.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.07/1.49  --res_passive_queues_freq               [15;5]
% 7.07/1.49  --res_forward_subs                      full
% 7.07/1.49  --res_backward_subs                     full
% 7.07/1.49  --res_forward_subs_resolution           true
% 7.07/1.49  --res_backward_subs_resolution          true
% 7.07/1.49  --res_orphan_elimination                true
% 7.07/1.49  --res_time_limit                        2.
% 7.07/1.49  --res_out_proof                         true
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Options
% 7.07/1.49  
% 7.07/1.49  --superposition_flag                    true
% 7.07/1.49  --sup_passive_queue_type                priority_queues
% 7.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.07/1.49  --demod_completeness_check              fast
% 7.07/1.49  --demod_use_ground                      true
% 7.07/1.49  --sup_to_prop_solver                    passive
% 7.07/1.49  --sup_prop_simpl_new                    true
% 7.07/1.49  --sup_prop_simpl_given                  true
% 7.07/1.49  --sup_fun_splitting                     false
% 7.07/1.49  --sup_smt_interval                      50000
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Simplification Setup
% 7.07/1.49  
% 7.07/1.49  --sup_indices_passive                   []
% 7.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_full_bw                           [BwDemod]
% 7.07/1.49  --sup_immed_triv                        [TrivRules]
% 7.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_immed_bw_main                     []
% 7.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  
% 7.07/1.49  ------ Combination Options
% 7.07/1.49  
% 7.07/1.49  --comb_res_mult                         3
% 7.07/1.49  --comb_sup_mult                         2
% 7.07/1.49  --comb_inst_mult                        10
% 7.07/1.49  
% 7.07/1.49  ------ Debug Options
% 7.07/1.49  
% 7.07/1.49  --dbg_backtrace                         false
% 7.07/1.49  --dbg_dump_prop_clauses                 false
% 7.07/1.49  --dbg_dump_prop_clauses_file            -
% 7.07/1.49  --dbg_out_stat                          false
% 7.07/1.49  ------ Parsing...
% 7.07/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.07/1.49  ------ Proving...
% 7.07/1.49  ------ Problem Properties 
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  clauses                                 33
% 7.07/1.49  conjectures                             1
% 7.07/1.49  EPR                                     3
% 7.07/1.49  Horn                                    25
% 7.07/1.49  unary                                   3
% 7.07/1.49  binary                                  8
% 7.07/1.49  lits                                    96
% 7.07/1.49  lits eq                                 14
% 7.07/1.49  fd_pure                                 0
% 7.07/1.49  fd_pseudo                               0
% 7.07/1.49  fd_cond                                 0
% 7.07/1.49  fd_pseudo_cond                          6
% 7.07/1.49  AC symbols                              0
% 7.07/1.49  
% 7.07/1.49  ------ Schedule dynamic 5 is on 
% 7.07/1.49  
% 7.07/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  ------ 
% 7.07/1.49  Current options:
% 7.07/1.49  ------ 
% 7.07/1.49  
% 7.07/1.49  ------ Input Options
% 7.07/1.49  
% 7.07/1.49  --out_options                           all
% 7.07/1.49  --tptp_safe_out                         true
% 7.07/1.49  --problem_path                          ""
% 7.07/1.49  --include_path                          ""
% 7.07/1.49  --clausifier                            res/vclausify_rel
% 7.07/1.49  --clausifier_options                    --mode clausify
% 7.07/1.49  --stdin                                 false
% 7.07/1.49  --stats_out                             all
% 7.07/1.49  
% 7.07/1.49  ------ General Options
% 7.07/1.49  
% 7.07/1.49  --fof                                   false
% 7.07/1.49  --time_out_real                         305.
% 7.07/1.49  --time_out_virtual                      -1.
% 7.07/1.49  --symbol_type_check                     false
% 7.07/1.49  --clausify_out                          false
% 7.07/1.49  --sig_cnt_out                           false
% 7.07/1.49  --trig_cnt_out                          false
% 7.07/1.49  --trig_cnt_out_tolerance                1.
% 7.07/1.49  --trig_cnt_out_sk_spl                   false
% 7.07/1.49  --abstr_cl_out                          false
% 7.07/1.49  
% 7.07/1.49  ------ Global Options
% 7.07/1.49  
% 7.07/1.49  --schedule                              default
% 7.07/1.49  --add_important_lit                     false
% 7.07/1.49  --prop_solver_per_cl                    1000
% 7.07/1.49  --min_unsat_core                        false
% 7.07/1.49  --soft_assumptions                      false
% 7.07/1.49  --soft_lemma_size                       3
% 7.07/1.49  --prop_impl_unit_size                   0
% 7.07/1.49  --prop_impl_unit                        []
% 7.07/1.49  --share_sel_clauses                     true
% 7.07/1.49  --reset_solvers                         false
% 7.07/1.49  --bc_imp_inh                            [conj_cone]
% 7.07/1.49  --conj_cone_tolerance                   3.
% 7.07/1.49  --extra_neg_conj                        none
% 7.07/1.49  --large_theory_mode                     true
% 7.07/1.49  --prolific_symb_bound                   200
% 7.07/1.49  --lt_threshold                          2000
% 7.07/1.49  --clause_weak_htbl                      true
% 7.07/1.49  --gc_record_bc_elim                     false
% 7.07/1.49  
% 7.07/1.49  ------ Preprocessing Options
% 7.07/1.49  
% 7.07/1.49  --preprocessing_flag                    true
% 7.07/1.49  --time_out_prep_mult                    0.1
% 7.07/1.49  --splitting_mode                        input
% 7.07/1.49  --splitting_grd                         true
% 7.07/1.49  --splitting_cvd                         false
% 7.07/1.49  --splitting_cvd_svl                     false
% 7.07/1.49  --splitting_nvd                         32
% 7.07/1.49  --sub_typing                            true
% 7.07/1.49  --prep_gs_sim                           true
% 7.07/1.49  --prep_unflatten                        true
% 7.07/1.49  --prep_res_sim                          true
% 7.07/1.49  --prep_upred                            true
% 7.07/1.49  --prep_sem_filter                       exhaustive
% 7.07/1.49  --prep_sem_filter_out                   false
% 7.07/1.49  --pred_elim                             true
% 7.07/1.49  --res_sim_input                         true
% 7.07/1.49  --eq_ax_congr_red                       true
% 7.07/1.49  --pure_diseq_elim                       true
% 7.07/1.49  --brand_transform                       false
% 7.07/1.49  --non_eq_to_eq                          false
% 7.07/1.49  --prep_def_merge                        true
% 7.07/1.49  --prep_def_merge_prop_impl              false
% 7.07/1.49  --prep_def_merge_mbd                    true
% 7.07/1.49  --prep_def_merge_tr_red                 false
% 7.07/1.49  --prep_def_merge_tr_cl                  false
% 7.07/1.49  --smt_preprocessing                     true
% 7.07/1.49  --smt_ac_axioms                         fast
% 7.07/1.49  --preprocessed_out                      false
% 7.07/1.49  --preprocessed_stats                    false
% 7.07/1.49  
% 7.07/1.49  ------ Abstraction refinement Options
% 7.07/1.49  
% 7.07/1.49  --abstr_ref                             []
% 7.07/1.49  --abstr_ref_prep                        false
% 7.07/1.49  --abstr_ref_until_sat                   false
% 7.07/1.49  --abstr_ref_sig_restrict                funpre
% 7.07/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.07/1.49  --abstr_ref_under                       []
% 7.07/1.49  
% 7.07/1.49  ------ SAT Options
% 7.07/1.49  
% 7.07/1.49  --sat_mode                              false
% 7.07/1.49  --sat_fm_restart_options                ""
% 7.07/1.49  --sat_gr_def                            false
% 7.07/1.49  --sat_epr_types                         true
% 7.07/1.49  --sat_non_cyclic_types                  false
% 7.07/1.49  --sat_finite_models                     false
% 7.07/1.49  --sat_fm_lemmas                         false
% 7.07/1.49  --sat_fm_prep                           false
% 7.07/1.49  --sat_fm_uc_incr                        true
% 7.07/1.49  --sat_out_model                         small
% 7.07/1.49  --sat_out_clauses                       false
% 7.07/1.49  
% 7.07/1.49  ------ QBF Options
% 7.07/1.49  
% 7.07/1.49  --qbf_mode                              false
% 7.07/1.49  --qbf_elim_univ                         false
% 7.07/1.49  --qbf_dom_inst                          none
% 7.07/1.49  --qbf_dom_pre_inst                      false
% 7.07/1.49  --qbf_sk_in                             false
% 7.07/1.49  --qbf_pred_elim                         true
% 7.07/1.49  --qbf_split                             512
% 7.07/1.49  
% 7.07/1.49  ------ BMC1 Options
% 7.07/1.49  
% 7.07/1.49  --bmc1_incremental                      false
% 7.07/1.49  --bmc1_axioms                           reachable_all
% 7.07/1.49  --bmc1_min_bound                        0
% 7.07/1.49  --bmc1_max_bound                        -1
% 7.07/1.49  --bmc1_max_bound_default                -1
% 7.07/1.49  --bmc1_symbol_reachability              true
% 7.07/1.49  --bmc1_property_lemmas                  false
% 7.07/1.49  --bmc1_k_induction                      false
% 7.07/1.49  --bmc1_non_equiv_states                 false
% 7.07/1.49  --bmc1_deadlock                         false
% 7.07/1.49  --bmc1_ucm                              false
% 7.07/1.49  --bmc1_add_unsat_core                   none
% 7.07/1.49  --bmc1_unsat_core_children              false
% 7.07/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.07/1.49  --bmc1_out_stat                         full
% 7.07/1.49  --bmc1_ground_init                      false
% 7.07/1.49  --bmc1_pre_inst_next_state              false
% 7.07/1.49  --bmc1_pre_inst_state                   false
% 7.07/1.49  --bmc1_pre_inst_reach_state             false
% 7.07/1.49  --bmc1_out_unsat_core                   false
% 7.07/1.49  --bmc1_aig_witness_out                  false
% 7.07/1.49  --bmc1_verbose                          false
% 7.07/1.49  --bmc1_dump_clauses_tptp                false
% 7.07/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.07/1.49  --bmc1_dump_file                        -
% 7.07/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.07/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.07/1.49  --bmc1_ucm_extend_mode                  1
% 7.07/1.49  --bmc1_ucm_init_mode                    2
% 7.07/1.49  --bmc1_ucm_cone_mode                    none
% 7.07/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.07/1.49  --bmc1_ucm_relax_model                  4
% 7.07/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.07/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.07/1.49  --bmc1_ucm_layered_model                none
% 7.07/1.49  --bmc1_ucm_max_lemma_size               10
% 7.07/1.49  
% 7.07/1.49  ------ AIG Options
% 7.07/1.49  
% 7.07/1.49  --aig_mode                              false
% 7.07/1.49  
% 7.07/1.49  ------ Instantiation Options
% 7.07/1.49  
% 7.07/1.49  --instantiation_flag                    true
% 7.07/1.49  --inst_sos_flag                         false
% 7.07/1.49  --inst_sos_phase                        true
% 7.07/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.07/1.49  --inst_lit_sel_side                     none
% 7.07/1.49  --inst_solver_per_active                1400
% 7.07/1.49  --inst_solver_calls_frac                1.
% 7.07/1.49  --inst_passive_queue_type               priority_queues
% 7.07/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.07/1.49  --inst_passive_queues_freq              [25;2]
% 7.07/1.49  --inst_dismatching                      true
% 7.07/1.49  --inst_eager_unprocessed_to_passive     true
% 7.07/1.49  --inst_prop_sim_given                   true
% 7.07/1.49  --inst_prop_sim_new                     false
% 7.07/1.49  --inst_subs_new                         false
% 7.07/1.49  --inst_eq_res_simp                      false
% 7.07/1.49  --inst_subs_given                       false
% 7.07/1.49  --inst_orphan_elimination               true
% 7.07/1.49  --inst_learning_loop_flag               true
% 7.07/1.49  --inst_learning_start                   3000
% 7.07/1.49  --inst_learning_factor                  2
% 7.07/1.49  --inst_start_prop_sim_after_learn       3
% 7.07/1.49  --inst_sel_renew                        solver
% 7.07/1.49  --inst_lit_activity_flag                true
% 7.07/1.49  --inst_restr_to_given                   false
% 7.07/1.49  --inst_activity_threshold               500
% 7.07/1.49  --inst_out_proof                        true
% 7.07/1.49  
% 7.07/1.49  ------ Resolution Options
% 7.07/1.49  
% 7.07/1.49  --resolution_flag                       false
% 7.07/1.49  --res_lit_sel                           adaptive
% 7.07/1.49  --res_lit_sel_side                      none
% 7.07/1.49  --res_ordering                          kbo
% 7.07/1.49  --res_to_prop_solver                    active
% 7.07/1.49  --res_prop_simpl_new                    false
% 7.07/1.49  --res_prop_simpl_given                  true
% 7.07/1.49  --res_passive_queue_type                priority_queues
% 7.07/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.07/1.49  --res_passive_queues_freq               [15;5]
% 7.07/1.49  --res_forward_subs                      full
% 7.07/1.49  --res_backward_subs                     full
% 7.07/1.49  --res_forward_subs_resolution           true
% 7.07/1.49  --res_backward_subs_resolution          true
% 7.07/1.49  --res_orphan_elimination                true
% 7.07/1.49  --res_time_limit                        2.
% 7.07/1.49  --res_out_proof                         true
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Options
% 7.07/1.49  
% 7.07/1.49  --superposition_flag                    true
% 7.07/1.49  --sup_passive_queue_type                priority_queues
% 7.07/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.07/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.07/1.49  --demod_completeness_check              fast
% 7.07/1.49  --demod_use_ground                      true
% 7.07/1.49  --sup_to_prop_solver                    passive
% 7.07/1.49  --sup_prop_simpl_new                    true
% 7.07/1.49  --sup_prop_simpl_given                  true
% 7.07/1.49  --sup_fun_splitting                     false
% 7.07/1.49  --sup_smt_interval                      50000
% 7.07/1.49  
% 7.07/1.49  ------ Superposition Simplification Setup
% 7.07/1.49  
% 7.07/1.49  --sup_indices_passive                   []
% 7.07/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.07/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.07/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_full_bw                           [BwDemod]
% 7.07/1.49  --sup_immed_triv                        [TrivRules]
% 7.07/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.07/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_immed_bw_main                     []
% 7.07/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.07/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.07/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.07/1.49  
% 7.07/1.49  ------ Combination Options
% 7.07/1.49  
% 7.07/1.49  --comb_res_mult                         3
% 7.07/1.49  --comb_sup_mult                         2
% 7.07/1.49  --comb_inst_mult                        10
% 7.07/1.49  
% 7.07/1.49  ------ Debug Options
% 7.07/1.49  
% 7.07/1.49  --dbg_backtrace                         false
% 7.07/1.49  --dbg_dump_prop_clauses                 false
% 7.07/1.49  --dbg_dump_prop_clauses_file            -
% 7.07/1.49  --dbg_out_stat                          false
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  ------ Proving...
% 7.07/1.49  
% 7.07/1.49  
% 7.07/1.49  % SZS status Theorem for theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.07/1.49  
% 7.07/1.49  fof(f5,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f13,plain,(
% 7.07/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.07/1.49    inference(ennf_transformation,[],[f5])).
% 7.07/1.49  
% 7.07/1.49  fof(f14,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.07/1.49    inference(flattening,[],[f13])).
% 7.07/1.49  
% 7.07/1.49  fof(f65,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f14])).
% 7.07/1.49  
% 7.07/1.49  fof(f11,conjecture,(
% 7.07/1.49    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f12,negated_conjecture,(
% 7.07/1.49    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.07/1.49    inference(negated_conjecture,[],[f11])).
% 7.07/1.49  
% 7.07/1.49  fof(f22,plain,(
% 7.07/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 7.07/1.49    inference(ennf_transformation,[],[f12])).
% 7.07/1.49  
% 7.07/1.49  fof(f50,plain,(
% 7.07/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) | ~v1_funct_2(sK13,sK11,sK12) | ~v1_funct_1(sK13)) & r2_hidden(sK13,k1_funct_2(sK11,sK12)))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f51,plain,(
% 7.07/1.49    (~m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) | ~v1_funct_2(sK13,sK11,sK12) | ~v1_funct_1(sK13)) & r2_hidden(sK13,k1_funct_2(sK11,sK12))),
% 7.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f22,f50])).
% 7.07/1.49  
% 7.07/1.49  fof(f88,plain,(
% 7.07/1.49    r2_hidden(sK13,k1_funct_2(sK11,sK12))),
% 7.07/1.49    inference(cnf_transformation,[],[f51])).
% 7.07/1.49  
% 7.07/1.49  fof(f9,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f23,plain,(
% 7.07/1.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.07/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.07/1.49  
% 7.07/1.49  fof(f24,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 7.07/1.49    inference(definition_folding,[],[f9,f23])).
% 7.07/1.49  
% 7.07/1.49  fof(f49,plain,(
% 7.07/1.49    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 7.07/1.49    inference(nnf_transformation,[],[f24])).
% 7.07/1.49  
% 7.07/1.49  fof(f83,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 7.07/1.49    inference(cnf_transformation,[],[f49])).
% 7.07/1.49  
% 7.07/1.49  fof(f99,plain,(
% 7.07/1.49    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 7.07/1.49    inference(equality_resolution,[],[f83])).
% 7.07/1.49  
% 7.07/1.49  fof(f43,plain,(
% 7.07/1.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 7.07/1.49    inference(nnf_transformation,[],[f23])).
% 7.07/1.49  
% 7.07/1.49  fof(f44,plain,(
% 7.07/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.07/1.49    inference(rectify,[],[f43])).
% 7.07/1.49  
% 7.07/1.49  fof(f47,plain,(
% 7.07/1.49    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X0) & k1_relat_1(sK10(X0,X1,X6)) = X1 & sK10(X0,X1,X6) = X6 & v1_funct_1(sK10(X0,X1,X6)) & v1_relat_1(sK10(X0,X1,X6))))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f46,plain,(
% 7.07/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X0) & k1_relat_1(sK9(X0,X1,X2)) = X1 & sK9(X0,X1,X2) = X3 & v1_funct_1(sK9(X0,X1,X2)) & v1_relat_1(sK9(X0,X1,X2))))) )),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f45,plain,(
% 7.07/1.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK8(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK8(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f48,plain,(
% 7.07/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK8(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X0) & k1_relat_1(sK9(X0,X1,X2)) = X1 & sK8(X0,X1,X2) = sK9(X0,X1,X2) & v1_funct_1(sK9(X0,X1,X2)) & v1_relat_1(sK9(X0,X1,X2))) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X0) & k1_relat_1(sK10(X0,X1,X6)) = X1 & sK10(X0,X1,X6) = X6 & v1_funct_1(sK10(X0,X1,X6)) & v1_relat_1(sK10(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f44,f47,f46,f45])).
% 7.07/1.49  
% 7.07/1.49  fof(f74,plain,(
% 7.07/1.49    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK10(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f73,plain,(
% 7.07/1.49    ( ! [X6,X2,X0,X1] : (sK10(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f8,axiom,(
% 7.07/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f18,plain,(
% 7.07/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.07/1.49    inference(ennf_transformation,[],[f8])).
% 7.07/1.49  
% 7.07/1.49  fof(f19,plain,(
% 7.07/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.07/1.49    inference(flattening,[],[f18])).
% 7.07/1.49  
% 7.07/1.49  fof(f70,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f19])).
% 7.07/1.49  
% 7.07/1.49  fof(f10,axiom,(
% 7.07/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f20,plain,(
% 7.07/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.07/1.49    inference(ennf_transformation,[],[f10])).
% 7.07/1.49  
% 7.07/1.49  fof(f21,plain,(
% 7.07/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.07/1.49    inference(flattening,[],[f20])).
% 7.07/1.49  
% 7.07/1.49  fof(f86,plain,(
% 7.07/1.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f21])).
% 7.07/1.49  
% 7.07/1.49  fof(f87,plain,(
% 7.07/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f21])).
% 7.07/1.49  
% 7.07/1.49  fof(f6,axiom,(
% 7.07/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f15,plain,(
% 7.07/1.49    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.07/1.49    inference(ennf_transformation,[],[f6])).
% 7.07/1.49  
% 7.07/1.49  fof(f16,plain,(
% 7.07/1.49    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.07/1.49    inference(flattening,[],[f15])).
% 7.07/1.49  
% 7.07/1.49  fof(f67,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.07/1.49    inference(cnf_transformation,[],[f16])).
% 7.07/1.49  
% 7.07/1.49  fof(f89,plain,(
% 7.07/1.49    ~m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) | ~v1_funct_2(sK13,sK11,sK12) | ~v1_funct_1(sK13)),
% 7.07/1.49    inference(cnf_transformation,[],[f51])).
% 7.07/1.49  
% 7.07/1.49  fof(f2,axiom,(
% 7.07/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f29,plain,(
% 7.07/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.07/1.49    inference(nnf_transformation,[],[f2])).
% 7.07/1.49  
% 7.07/1.49  fof(f30,plain,(
% 7.07/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.07/1.49    inference(flattening,[],[f29])).
% 7.07/1.49  
% 7.07/1.49  fof(f54,plain,(
% 7.07/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.07/1.49    inference(cnf_transformation,[],[f30])).
% 7.07/1.49  
% 7.07/1.49  fof(f91,plain,(
% 7.07/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.07/1.49    inference(equality_resolution,[],[f54])).
% 7.07/1.49  
% 7.07/1.49  fof(f56,plain,(
% 7.07/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f30])).
% 7.07/1.49  
% 7.07/1.49  fof(f72,plain,(
% 7.07/1.49    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK10(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f71,plain,(
% 7.07/1.49    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK10(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f75,plain,(
% 7.07/1.49    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f48])).
% 7.07/1.49  
% 7.07/1.49  fof(f1,axiom,(
% 7.07/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f25,plain,(
% 7.07/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.07/1.49    inference(nnf_transformation,[],[f1])).
% 7.07/1.49  
% 7.07/1.49  fof(f26,plain,(
% 7.07/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.07/1.49    inference(rectify,[],[f25])).
% 7.07/1.49  
% 7.07/1.49  fof(f27,plain,(
% 7.07/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f28,plain,(
% 7.07/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 7.07/1.49  
% 7.07/1.49  fof(f53,plain,(
% 7.07/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f28])).
% 7.07/1.49  
% 7.07/1.49  fof(f3,axiom,(
% 7.07/1.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f31,plain,(
% 7.07/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 7.07/1.49    inference(nnf_transformation,[],[f3])).
% 7.07/1.49  
% 7.07/1.49  fof(f32,plain,(
% 7.07/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.07/1.49    inference(rectify,[],[f31])).
% 7.07/1.49  
% 7.07/1.49  fof(f35,plain,(
% 7.07/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f34,plain,(
% 7.07/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f33,plain,(
% 7.07/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f36,plain,(
% 7.07/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).
% 7.07/1.49  
% 7.07/1.49  fof(f57,plain,(
% 7.07/1.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 7.07/1.49    inference(cnf_transformation,[],[f36])).
% 7.07/1.49  
% 7.07/1.49  fof(f93,plain,(
% 7.07/1.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 7.07/1.49    inference(equality_resolution,[],[f57])).
% 7.07/1.49  
% 7.07/1.49  fof(f4,axiom,(
% 7.07/1.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f37,plain,(
% 7.07/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.07/1.49    inference(nnf_transformation,[],[f4])).
% 7.07/1.49  
% 7.07/1.49  fof(f38,plain,(
% 7.07/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.07/1.49    inference(rectify,[],[f37])).
% 7.07/1.49  
% 7.07/1.49  fof(f41,plain,(
% 7.07/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f40,plain,(
% 7.07/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK6(X0,X1),X2),X0))) )),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f39,plain,(
% 7.07/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 7.07/1.49    introduced(choice_axiom,[])).
% 7.07/1.49  
% 7.07/1.49  fof(f42,plain,(
% 7.07/1.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.07/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f38,f41,f40,f39])).
% 7.07/1.49  
% 7.07/1.49  fof(f62,plain,(
% 7.07/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 7.07/1.49    inference(cnf_transformation,[],[f42])).
% 7.07/1.49  
% 7.07/1.49  fof(f94,plain,(
% 7.07/1.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 7.07/1.49    inference(equality_resolution,[],[f62])).
% 7.07/1.49  
% 7.07/1.49  fof(f52,plain,(
% 7.07/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f28])).
% 7.07/1.49  
% 7.07/1.49  fof(f7,axiom,(
% 7.07/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 7.07/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.07/1.49  
% 7.07/1.49  fof(f17,plain,(
% 7.07/1.49    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.07/1.49    inference(ennf_transformation,[],[f7])).
% 7.07/1.49  
% 7.07/1.49  fof(f68,plain,(
% 7.07/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.07/1.49    inference(cnf_transformation,[],[f17])).
% 7.07/1.49  
% 7.07/1.49  cnf(c_13,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.07/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.07/1.49      | ~ v1_relat_1(X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5153,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.07/1.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.07/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.07/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_37,negated_conjecture,
% 7.07/1.49      ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
% 7.07/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5137,plain,
% 7.07/1.49      ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_32,plain,
% 7.07/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 7.07/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5139,plain,
% 7.07/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_27,plain,
% 7.07/1.49      ( ~ sP0(X0,X1,X2)
% 7.07/1.49      | ~ r2_hidden(X3,X2)
% 7.07/1.49      | k1_relat_1(sK10(X0,X1,X3)) = X1 ),
% 7.07/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5144,plain,
% 7.07/1.49      ( k1_relat_1(sK10(X0,X1,X2)) = X1
% 7.07/1.49      | sP0(X0,X1,X3) != iProver_top
% 7.07/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_7023,plain,
% 7.07/1.49      ( k1_relat_1(sK10(X0,X1,X2)) = X1
% 7.07/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_5139,c_5144]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_12850,plain,
% 7.07/1.49      ( k1_relat_1(sK10(sK12,sK11,sK13)) = sK11 ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_5137,c_7023]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_28,plain,
% 7.07/1.49      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK10(X0,X1,X3) = X3 ),
% 7.07/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5143,plain,
% 7.07/1.49      ( sK10(X0,X1,X2) = X2
% 7.07/1.49      | sP0(X0,X1,X3) != iProver_top
% 7.07/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_6591,plain,
% 7.07/1.49      ( sK10(X0,X1,X2) = X2
% 7.07/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_5139,c_5143]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_7824,plain,
% 7.07/1.49      ( sK10(sK12,sK11,sK13) = sK13 ),
% 7.07/1.49      inference(superposition,[status(thm)],[c_5137,c_6591]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_12852,plain,
% 7.07/1.49      ( k1_relat_1(sK13) = sK11 ),
% 7.07/1.49      inference(light_normalisation,[status(thm)],[c_12850,c_7824]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_17,plain,
% 7.07/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.07/1.49      | v1_partfun1(X0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | ~ v1_funct_1(X0)
% 7.07/1.49      | v1_xboole_0(X2) ),
% 7.07/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_34,plain,
% 7.07/1.49      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.07/1.49      | ~ v1_funct_1(X0)
% 7.07/1.49      | ~ v1_relat_1(X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_552,plain,
% 7.07/1.49      ( v1_partfun1(X0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | ~ v1_funct_1(X0)
% 7.07/1.49      | ~ v1_funct_1(X3)
% 7.07/1.49      | ~ v1_relat_1(X3)
% 7.07/1.49      | v1_xboole_0(X2)
% 7.07/1.49      | X3 != X0
% 7.07/1.49      | k2_relat_1(X3) != X2
% 7.07/1.49      | k1_relat_1(X3) != X1 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_553,plain,
% 7.07/1.49      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.07/1.49      | ~ v1_funct_1(X0)
% 7.07/1.49      | ~ v1_relat_1(X0)
% 7.07/1.49      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_552]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_33,plain,
% 7.07/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.07/1.49      | ~ v1_funct_1(X0)
% 7.07/1.49      | ~ v1_relat_1(X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_557,plain,
% 7.07/1.49      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.07/1.49      | ~ v1_funct_1(X0)
% 7.07/1.49      | ~ v1_relat_1(X0)
% 7.07/1.49      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.07/1.49      inference(global_propositional_subsumption,
% 7.07/1.49                [status(thm)],
% 7.07/1.49                [c_553,c_33]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_14,plain,
% 7.07/1.49      ( v1_funct_2(X0,X1,X2)
% 7.07/1.49      | ~ v1_partfun1(X0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | ~ v1_funct_1(X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_36,negated_conjecture,
% 7.07/1.49      ( ~ v1_funct_2(sK13,sK11,sK12)
% 7.07/1.49      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.07/1.49      | ~ v1_funct_1(sK13) ),
% 7.07/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_576,plain,
% 7.07/1.49      ( ~ v1_partfun1(X0,X1)
% 7.07/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.49      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.07/1.49      | ~ v1_funct_1(X0)
% 7.07/1.49      | ~ v1_funct_1(sK13)
% 7.07/1.49      | sK12 != X2
% 7.07/1.49      | sK11 != X1
% 7.07/1.49      | sK13 != X0 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_36]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_577,plain,
% 7.07/1.49      ( ~ v1_partfun1(sK13,sK11)
% 7.07/1.49      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.07/1.49      | ~ v1_funct_1(sK13) ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_576]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_641,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.07/1.49      | ~ v1_funct_1(X0)
% 7.07/1.49      | ~ v1_funct_1(sK13)
% 7.07/1.49      | ~ v1_relat_1(X0)
% 7.07/1.49      | v1_xboole_0(k2_relat_1(X0))
% 7.07/1.49      | k1_relat_1(X0) != sK11
% 7.07/1.49      | sK13 != X0 ),
% 7.07/1.49      inference(resolution_lifted,[status(thm)],[c_557,c_577]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_642,plain,
% 7.07/1.49      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.07/1.49      | ~ v1_funct_1(sK13)
% 7.07/1.49      | ~ v1_relat_1(sK13)
% 7.07/1.49      | v1_xboole_0(k2_relat_1(sK13))
% 7.07/1.49      | k1_relat_1(sK13) != sK11 ),
% 7.07/1.49      inference(unflattening,[status(thm)],[c_641]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5133,plain,
% 7.07/1.49      ( k1_relat_1(sK13) != sK11
% 7.07/1.49      | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.07/1.49      | v1_funct_1(sK13) != iProver_top
% 7.07/1.49      | v1_relat_1(sK13) != iProver_top
% 7.07/1.49      | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_13723,plain,
% 7.07/1.49      ( sK11 != sK11
% 7.07/1.49      | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.07/1.49      | v1_funct_1(sK13) != iProver_top
% 7.07/1.49      | v1_relat_1(sK13) != iProver_top
% 7.07/1.49      | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
% 7.07/1.49      inference(demodulation,[status(thm)],[c_12852,c_5133]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_13734,plain,
% 7.07/1.49      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.07/1.49      | v1_funct_1(sK13) != iProver_top
% 7.07/1.49      | v1_relat_1(sK13) != iProver_top
% 7.07/1.49      | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
% 7.07/1.49      inference(equality_resolution_simp,[status(thm)],[c_13723]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_38,plain,
% 7.07/1.49      ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_4,plain,
% 7.07/1.49      ( r1_tarski(X0,X0) ),
% 7.07/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_128,plain,
% 7.07/1.49      ( r1_tarski(sK13,sK13) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_2,plain,
% 7.07/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.07/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_132,plain,
% 7.07/1.49      ( ~ r1_tarski(sK13,sK13) | sK13 = sK13 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_643,plain,
% 7.07/1.49      ( k1_relat_1(sK13) != sK11
% 7.07/1.49      | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.07/1.49      | v1_funct_1(sK13) != iProver_top
% 7.07/1.49      | v1_relat_1(sK13) != iProver_top
% 7.07/1.49      | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_29,plain,
% 7.07/1.49      ( ~ sP0(X0,X1,X2)
% 7.07/1.49      | ~ r2_hidden(X3,X2)
% 7.07/1.49      | v1_funct_1(sK10(X0,X1,X3)) ),
% 7.07/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5442,plain,
% 7.07/1.49      ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
% 7.07/1.49      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.07/1.49      | v1_funct_1(sK10(X0,X1,sK13)) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_29]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5536,plain,
% 7.07/1.49      ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
% 7.07/1.49      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.07/1.49      | v1_funct_1(sK10(sK12,sK11,sK13)) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_5442]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5538,plain,
% 7.07/1.49      ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
% 7.07/1.49      | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top
% 7.07/1.49      | v1_funct_1(sK10(sK12,sK11,sK13)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_5536]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5537,plain,
% 7.07/1.49      ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_32]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5540,plain,
% 7.07/1.49      ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_5537]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_4542,plain,
% 7.07/1.49      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.07/1.49      theory(equality) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5672,plain,
% 7.07/1.49      ( v1_funct_1(X0)
% 7.07/1.49      | ~ v1_funct_1(sK10(sK12,sK11,sK13))
% 7.07/1.49      | X0 != sK10(sK12,sK11,sK13) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_4542]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5673,plain,
% 7.07/1.49      ( X0 != sK10(sK12,sK11,sK13)
% 7.07/1.49      | v1_funct_1(X0) = iProver_top
% 7.07/1.49      | v1_funct_1(sK10(sK12,sK11,sK13)) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_5672]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5675,plain,
% 7.07/1.49      ( sK13 != sK10(sK12,sK11,sK13)
% 7.07/1.49      | v1_funct_1(sK10(sK12,sK11,sK13)) != iProver_top
% 7.07/1.49      | v1_funct_1(sK13) = iProver_top ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_5673]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_30,plain,
% 7.07/1.49      ( ~ sP0(X0,X1,X2)
% 7.07/1.49      | ~ r2_hidden(X3,X2)
% 7.07/1.49      | v1_relat_1(sK10(X0,X1,X3)) ),
% 7.07/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5447,plain,
% 7.07/1.49      ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
% 7.07/1.49      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.07/1.49      | v1_relat_1(sK10(X0,X1,sK13)) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_30]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5690,plain,
% 7.07/1.49      ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
% 7.07/1.49      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.07/1.49      | v1_relat_1(sK10(sK12,sK11,sK13)) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_5447]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5692,plain,
% 7.07/1.49      ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
% 7.07/1.49      | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top
% 7.07/1.49      | v1_relat_1(sK10(sK12,sK11,sK13)) = iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_5690]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5482,plain,
% 7.07/1.49      ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
% 7.07/1.49      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.07/1.49      | sK10(X0,X1,sK13) = sK13 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5688,plain,
% 7.07/1.49      ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
% 7.07/1.49      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.07/1.49      | sK10(sK12,sK11,sK13) = sK13 ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_5482]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_4541,plain,
% 7.07/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.07/1.49      theory(equality) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5810,plain,
% 7.07/1.49      ( v1_relat_1(X0)
% 7.07/1.49      | ~ v1_relat_1(sK10(sK12,sK11,sK13))
% 7.07/1.49      | X0 != sK10(sK12,sK11,sK13) ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_4541]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5816,plain,
% 7.07/1.49      ( X0 != sK10(sK12,sK11,sK13)
% 7.07/1.49      | v1_relat_1(X0) = iProver_top
% 7.07/1.49      | v1_relat_1(sK10(sK12,sK11,sK13)) != iProver_top ),
% 7.07/1.49      inference(predicate_to_equality,[status(thm)],[c_5810]) ).
% 7.07/1.49  
% 7.07/1.49  cnf(c_5818,plain,
% 7.07/1.49      ( sK13 != sK10(sK12,sK11,sK13)
% 7.07/1.49      | v1_relat_1(sK10(sK12,sK11,sK13)) != iProver_top
% 7.07/1.49      | v1_relat_1(sK13) = iProver_top ),
% 7.07/1.49      inference(instantiation,[status(thm)],[c_5816]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_4531,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_6107,plain,
% 7.07/1.50      ( X0 != X1
% 7.07/1.50      | X0 = sK10(sK12,sK11,sK13)
% 7.07/1.50      | sK10(sK12,sK11,sK13) != X1 ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_4531]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_6108,plain,
% 7.07/1.50      ( sK10(sK12,sK11,sK13) != sK13
% 7.07/1.50      | sK13 = sK10(sK12,sK11,sK13)
% 7.07/1.50      | sK13 != sK13 ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_6107]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_21269,plain,
% 7.07/1.50      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.07/1.50      | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
% 7.07/1.50      inference(global_propositional_subsumption,
% 7.07/1.50                [status(thm)],
% 7.07/1.50                [c_13734,c_37,c_38,c_128,c_132,c_643,c_5538,c_5537,
% 7.07/1.50                 c_5540,c_5675,c_5692,c_5688,c_5818,c_6108,c_12852]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_21275,plain,
% 7.07/1.50      ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
% 7.07/1.50      | r1_tarski(k1_relat_1(sK13),sK11) != iProver_top
% 7.07/1.50      | v1_relat_1(sK13) != iProver_top
% 7.07/1.50      | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
% 7.07/1.50      inference(superposition,[status(thm)],[c_5153,c_21269]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_21276,plain,
% 7.07/1.50      ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
% 7.07/1.50      | r1_tarski(sK11,sK11) != iProver_top
% 7.07/1.50      | v1_relat_1(sK13) != iProver_top
% 7.07/1.50      | v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
% 7.07/1.50      inference(light_normalisation,[status(thm)],[c_21275,c_12852]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_26,plain,
% 7.07/1.50      ( ~ sP0(X0,X1,X2)
% 7.07/1.50      | r1_tarski(k2_relat_1(sK10(X0,X1,X3)),X0)
% 7.07/1.50      | ~ r2_hidden(X3,X2) ),
% 7.07/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5466,plain,
% 7.07/1.50      ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
% 7.07/1.50      | r1_tarski(k2_relat_1(sK10(X0,X1,sK13)),X0)
% 7.07/1.50      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_26]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5689,plain,
% 7.07/1.50      ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
% 7.07/1.50      | r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12)
% 7.07/1.50      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_5466]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5694,plain,
% 7.07/1.50      ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
% 7.07/1.50      | r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12) = iProver_top
% 7.07/1.50      | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top ),
% 7.07/1.50      inference(predicate_to_equality,[status(thm)],[c_5689]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_4534,plain,
% 7.07/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.07/1.50      theory(equality) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_7432,plain,
% 7.07/1.50      ( ~ r1_tarski(X0,sK12) | r1_tarski(X1,sK12) | X1 != X0 ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_4534]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_13705,plain,
% 7.07/1.50      ( r1_tarski(X0,sK12)
% 7.07/1.50      | ~ r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12)
% 7.07/1.50      | X0 != k2_relat_1(sK10(sK12,sK11,sK13)) ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_7432]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_15730,plain,
% 7.07/1.50      ( r1_tarski(k2_relat_1(X0),sK12)
% 7.07/1.50      | ~ r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12)
% 7.07/1.50      | k2_relat_1(X0) != k2_relat_1(sK10(sK12,sK11,sK13)) ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_13705]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_15732,plain,
% 7.07/1.50      ( k2_relat_1(X0) != k2_relat_1(sK10(sK12,sK11,sK13))
% 7.07/1.50      | r1_tarski(k2_relat_1(X0),sK12) = iProver_top
% 7.07/1.50      | r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12) != iProver_top ),
% 7.07/1.50      inference(predicate_to_equality,[status(thm)],[c_15730]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_15734,plain,
% 7.07/1.50      ( k2_relat_1(sK13) != k2_relat_1(sK10(sK12,sK11,sK13))
% 7.07/1.50      | r1_tarski(k2_relat_1(sK10(sK12,sK11,sK13)),sK12) != iProver_top
% 7.07/1.50      | r1_tarski(k2_relat_1(sK13),sK12) = iProver_top ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_15732]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_4537,plain,
% 7.07/1.50      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 7.07/1.50      theory(equality) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_15731,plain,
% 7.07/1.50      ( X0 != sK10(sK12,sK11,sK13)
% 7.07/1.50      | k2_relat_1(X0) = k2_relat_1(sK10(sK12,sK11,sK13)) ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_4537]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_15736,plain,
% 7.07/1.50      ( k2_relat_1(sK13) = k2_relat_1(sK10(sK12,sK11,sK13))
% 7.07/1.50      | sK13 != sK10(sK12,sK11,sK13) ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_15731]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_18612,plain,
% 7.07/1.50      ( r1_tarski(sK11,sK11) ),
% 7.07/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_18615,plain,
% 7.07/1.50      ( r1_tarski(sK11,sK11) = iProver_top ),
% 7.07/1.50      inference(predicate_to_equality,[status(thm)],[c_18612]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_21540,plain,
% 7.07/1.50      ( v1_xboole_0(k2_relat_1(sK13)) = iProver_top ),
% 7.07/1.50      inference(global_propositional_subsumption,
% 7.07/1.50                [status(thm)],
% 7.07/1.50                [c_21276,c_37,c_38,c_128,c_132,c_5537,c_5540,c_5692,
% 7.07/1.50                 c_5694,c_5688,c_5818,c_6108,c_15734,c_15736,c_18615]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_0,plain,
% 7.07/1.50      ( r2_hidden(sK1(X0),X0) | v1_xboole_0(X0) ),
% 7.07/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5165,plain,
% 7.07/1.50      ( r2_hidden(sK1(X0),X0) = iProver_top
% 7.07/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.07/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_8,plain,
% 7.07/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.07/1.50      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 7.07/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5158,plain,
% 7.07/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.07/1.50      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 7.07/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_11,plain,
% 7.07/1.50      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 7.07/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5155,plain,
% 7.07/1.50      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 7.07/1.50      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 7.07/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_6497,plain,
% 7.07/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.07/1.50      | r2_hidden(sK4(X1,X0),k2_relat_1(X1)) = iProver_top ),
% 7.07/1.50      inference(superposition,[status(thm)],[c_5158,c_5155]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_1,plain,
% 7.07/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.07/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5164,plain,
% 7.07/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.07/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.07/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_11539,plain,
% 7.07/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.07/1.50      | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
% 7.07/1.50      inference(superposition,[status(thm)],[c_6497,c_5164]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_11653,plain,
% 7.07/1.50      ( v1_xboole_0(k2_relat_1(X0)) != iProver_top
% 7.07/1.50      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 7.07/1.50      inference(superposition,[status(thm)],[c_5165,c_11539]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_21545,plain,
% 7.07/1.50      ( v1_xboole_0(k1_relat_1(sK13)) = iProver_top ),
% 7.07/1.50      inference(superposition,[status(thm)],[c_21540,c_11653]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_21556,plain,
% 7.07/1.50      ( v1_xboole_0(sK11) = iProver_top ),
% 7.07/1.50      inference(light_normalisation,[status(thm)],[c_21545,c_12852]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_16,plain,
% 7.07/1.50      ( v1_partfun1(X0,X1)
% 7.07/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.50      | ~ v1_xboole_0(X1) ),
% 7.07/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_623,plain,
% 7.07/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.07/1.50      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.07/1.50      | ~ v1_funct_1(sK13)
% 7.07/1.50      | ~ v1_xboole_0(X1)
% 7.07/1.50      | sK11 != X1
% 7.07/1.50      | sK13 != X0 ),
% 7.07/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_577]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_624,plain,
% 7.07/1.50      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0)))
% 7.07/1.50      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.07/1.50      | ~ v1_funct_1(sK13)
% 7.07/1.50      | ~ v1_xboole_0(sK11) ),
% 7.07/1.50      inference(unflattening,[status(thm)],[c_623]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_4528,plain,
% 7.07/1.50      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.07/1.50      | ~ v1_funct_1(sK13)
% 7.07/1.50      | ~ v1_xboole_0(sK11)
% 7.07/1.50      | sP0_iProver_split ),
% 7.07/1.50      inference(splitting,
% 7.07/1.50                [splitting(split),new_symbols(definition,[])],
% 7.07/1.50                [c_624]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5134,plain,
% 7.07/1.50      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.07/1.50      | v1_funct_1(sK13) != iProver_top
% 7.07/1.50      | v1_xboole_0(sK11) != iProver_top
% 7.07/1.50      | sP0_iProver_split = iProver_top ),
% 7.07/1.50      inference(predicate_to_equality,[status(thm)],[c_4528]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_4527,plain,
% 7.07/1.50      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0)))
% 7.07/1.50      | ~ sP0_iProver_split ),
% 7.07/1.50      inference(splitting,
% 7.07/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.07/1.50                [c_624]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5135,plain,
% 7.07/1.50      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0))) != iProver_top
% 7.07/1.50      | sP0_iProver_split != iProver_top ),
% 7.07/1.50      inference(predicate_to_equality,[status(thm)],[c_4527]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_5292,plain,
% 7.07/1.50      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.07/1.50      | v1_funct_1(sK13) != iProver_top
% 7.07/1.50      | v1_xboole_0(sK11) != iProver_top ),
% 7.07/1.50      inference(forward_subsumption_resolution,
% 7.07/1.50                [status(thm)],
% 7.07/1.50                [c_5134,c_5135]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_10038,plain,
% 7.07/1.50      ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
% 7.07/1.50      | r1_tarski(k1_relat_1(sK13),sK11) != iProver_top
% 7.07/1.50      | v1_funct_1(sK13) != iProver_top
% 7.07/1.50      | v1_relat_1(sK13) != iProver_top
% 7.07/1.50      | v1_xboole_0(sK11) != iProver_top ),
% 7.07/1.50      inference(superposition,[status(thm)],[c_5153,c_5292]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_10413,plain,
% 7.07/1.50      ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
% 7.07/1.50      | r1_tarski(k1_relat_1(sK13),sK11) != iProver_top
% 7.07/1.50      | v1_xboole_0(sK11) != iProver_top ),
% 7.07/1.50      inference(global_propositional_subsumption,
% 7.07/1.50                [status(thm)],
% 7.07/1.50                [c_10038,c_37,c_38,c_128,c_132,c_5538,c_5537,c_5540,
% 7.07/1.50                 c_5675,c_5692,c_5688,c_5818,c_6108]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(c_13721,plain,
% 7.07/1.50      ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
% 7.07/1.50      | r1_tarski(sK11,sK11) != iProver_top
% 7.07/1.50      | v1_xboole_0(sK11) != iProver_top ),
% 7.07/1.50      inference(demodulation,[status(thm)],[c_12852,c_10413]) ).
% 7.07/1.50  
% 7.07/1.50  cnf(contradiction,plain,
% 7.07/1.50      ( $false ),
% 7.07/1.50      inference(minisat,
% 7.07/1.50                [status(thm)],
% 7.07/1.50                [c_21556,c_18615,c_15736,c_15734,c_13721,c_6108,c_5688,
% 7.07/1.50                 c_5694,c_5540,c_5537,c_132,c_128,c_38,c_37]) ).
% 7.07/1.50  
% 7.07/1.50  
% 7.07/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.07/1.50  
% 7.07/1.50  ------                               Statistics
% 7.07/1.50  
% 7.07/1.50  ------ General
% 7.07/1.50  
% 7.07/1.50  abstr_ref_over_cycles:                  0
% 7.07/1.50  abstr_ref_under_cycles:                 0
% 7.07/1.50  gc_basic_clause_elim:                   0
% 7.07/1.50  forced_gc_time:                         0
% 7.07/1.50  parsing_time:                           0.013
% 7.07/1.50  unif_index_cands_time:                  0.
% 7.07/1.50  unif_index_add_time:                    0.
% 7.07/1.50  orderings_time:                         0.
% 7.07/1.50  out_proof_time:                         0.014
% 7.07/1.50  total_time:                             0.655
% 7.07/1.50  num_of_symbols:                         60
% 7.07/1.50  num_of_terms:                           20512
% 7.07/1.50  
% 7.07/1.50  ------ Preprocessing
% 7.07/1.50  
% 7.07/1.50  num_of_splits:                          1
% 7.07/1.50  num_of_split_atoms:                     1
% 7.07/1.50  num_of_reused_defs:                     0
% 7.07/1.50  num_eq_ax_congr_red:                    72
% 7.07/1.50  num_of_sem_filtered_clauses:            1
% 7.07/1.50  num_of_subtypes:                        0
% 7.07/1.50  monotx_restored_types:                  0
% 7.07/1.50  sat_num_of_epr_types:                   0
% 7.07/1.50  sat_num_of_non_cyclic_types:            0
% 7.07/1.50  sat_guarded_non_collapsed_types:        0
% 7.07/1.50  num_pure_diseq_elim:                    0
% 7.07/1.50  simp_replaced_by:                       0
% 7.07/1.50  res_preprocessed:                       165
% 7.07/1.50  prep_upred:                             0
% 7.07/1.50  prep_unflattend:                        156
% 7.07/1.50  smt_new_axioms:                         0
% 7.07/1.50  pred_elim_cands:                        7
% 7.07/1.50  pred_elim:                              2
% 7.07/1.50  pred_elim_cl:                           2
% 7.07/1.50  pred_elim_cycles:                       12
% 7.07/1.50  merged_defs:                            0
% 7.07/1.50  merged_defs_ncl:                        0
% 7.07/1.50  bin_hyper_res:                          0
% 7.07/1.50  prep_cycles:                            4
% 7.07/1.50  pred_elim_time:                         0.069
% 7.07/1.50  splitting_time:                         0.
% 7.07/1.50  sem_filter_time:                        0.
% 7.07/1.50  monotx_time:                            0.001
% 7.07/1.50  subtype_inf_time:                       0.
% 7.07/1.50  
% 7.07/1.50  ------ Problem properties
% 7.07/1.50  
% 7.07/1.50  clauses:                                33
% 7.07/1.50  conjectures:                            1
% 7.07/1.50  epr:                                    3
% 7.07/1.50  horn:                                   25
% 7.07/1.50  ground:                                 4
% 7.07/1.50  unary:                                  3
% 7.07/1.50  binary:                                 8
% 7.07/1.50  lits:                                   96
% 7.07/1.50  lits_eq:                                14
% 7.07/1.50  fd_pure:                                0
% 7.07/1.50  fd_pseudo:                              0
% 7.07/1.50  fd_cond:                                0
% 7.07/1.50  fd_pseudo_cond:                         6
% 7.07/1.50  ac_symbols:                             0
% 7.07/1.50  
% 7.07/1.50  ------ Propositional Solver
% 7.07/1.50  
% 7.07/1.50  prop_solver_calls:                      28
% 7.07/1.50  prop_fast_solver_calls:                 2235
% 7.07/1.50  smt_solver_calls:                       0
% 7.07/1.50  smt_fast_solver_calls:                  0
% 7.07/1.50  prop_num_of_clauses:                    7398
% 7.07/1.50  prop_preprocess_simplified:             14248
% 7.07/1.50  prop_fo_subsumed:                       51
% 7.07/1.50  prop_solver_time:                       0.
% 7.07/1.50  smt_solver_time:                        0.
% 7.07/1.50  smt_fast_solver_time:                   0.
% 7.07/1.50  prop_fast_solver_time:                  0.
% 7.07/1.50  prop_unsat_core_time:                   0.
% 7.07/1.50  
% 7.07/1.50  ------ QBF
% 7.07/1.50  
% 7.07/1.50  qbf_q_res:                              0
% 7.07/1.50  qbf_num_tautologies:                    0
% 7.07/1.50  qbf_prep_cycles:                        0
% 7.07/1.50  
% 7.07/1.50  ------ BMC1
% 7.07/1.50  
% 7.07/1.50  bmc1_current_bound:                     -1
% 7.07/1.50  bmc1_last_solved_bound:                 -1
% 7.07/1.50  bmc1_unsat_core_size:                   -1
% 7.07/1.50  bmc1_unsat_core_parents_size:           -1
% 7.07/1.50  bmc1_merge_next_fun:                    0
% 7.07/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.07/1.50  
% 7.07/1.50  ------ Instantiation
% 7.07/1.50  
% 7.07/1.50  inst_num_of_clauses:                    1593
% 7.07/1.50  inst_num_in_passive:                    329
% 7.07/1.50  inst_num_in_active:                     586
% 7.07/1.50  inst_num_in_unprocessed:                678
% 7.07/1.50  inst_num_of_loops:                      740
% 7.07/1.50  inst_num_of_learning_restarts:          0
% 7.07/1.50  inst_num_moves_active_passive:          151
% 7.07/1.50  inst_lit_activity:                      0
% 7.07/1.50  inst_lit_activity_moves:                0
% 7.07/1.50  inst_num_tautologies:                   0
% 7.07/1.50  inst_num_prop_implied:                  0
% 7.07/1.50  inst_num_existing_simplified:           0
% 7.07/1.50  inst_num_eq_res_simplified:             0
% 7.07/1.50  inst_num_child_elim:                    0
% 7.07/1.50  inst_num_of_dismatching_blockings:      1106
% 7.07/1.50  inst_num_of_non_proper_insts:           1501
% 7.07/1.50  inst_num_of_duplicates:                 0
% 7.07/1.50  inst_inst_num_from_inst_to_res:         0
% 7.07/1.50  inst_dismatching_checking_time:         0.
% 7.07/1.50  
% 7.07/1.50  ------ Resolution
% 7.07/1.50  
% 7.07/1.50  res_num_of_clauses:                     0
% 7.07/1.50  res_num_in_passive:                     0
% 7.07/1.50  res_num_in_active:                      0
% 7.07/1.50  res_num_of_loops:                       169
% 7.07/1.50  res_forward_subset_subsumed:            99
% 7.07/1.50  res_backward_subset_subsumed:           0
% 7.07/1.50  res_forward_subsumed:                   0
% 7.07/1.50  res_backward_subsumed:                  0
% 7.07/1.50  res_forward_subsumption_resolution:     2
% 7.07/1.50  res_backward_subsumption_resolution:    0
% 7.07/1.50  res_clause_to_clause_subsumption:       1817
% 7.07/1.50  res_orphan_elimination:                 0
% 7.07/1.50  res_tautology_del:                      75
% 7.07/1.50  res_num_eq_res_simplified:              0
% 7.07/1.50  res_num_sel_changes:                    0
% 7.07/1.50  res_moves_from_active_to_pass:          0
% 7.07/1.50  
% 7.07/1.50  ------ Superposition
% 7.07/1.50  
% 7.07/1.50  sup_time_total:                         0.
% 7.07/1.50  sup_time_generating:                    0.
% 7.07/1.50  sup_time_sim_full:                      0.
% 7.07/1.50  sup_time_sim_immed:                     0.
% 7.07/1.50  
% 7.07/1.50  sup_num_of_clauses:                     554
% 7.07/1.50  sup_num_in_active:                      136
% 7.07/1.50  sup_num_in_passive:                     418
% 7.07/1.50  sup_num_of_loops:                       146
% 7.07/1.50  sup_fw_superposition:                   486
% 7.07/1.50  sup_bw_superposition:                   161
% 7.07/1.50  sup_immediate_simplified:               22
% 7.07/1.50  sup_given_eliminated:                   0
% 7.07/1.50  comparisons_done:                       0
% 7.07/1.50  comparisons_avoided:                    0
% 7.07/1.50  
% 7.07/1.50  ------ Simplifications
% 7.07/1.50  
% 7.07/1.50  
% 7.07/1.50  sim_fw_subset_subsumed:                 1
% 7.07/1.50  sim_bw_subset_subsumed:                 7
% 7.07/1.50  sim_fw_subsumed:                        9
% 7.07/1.50  sim_bw_subsumed:                        0
% 7.07/1.50  sim_fw_subsumption_res:                 2
% 7.07/1.50  sim_bw_subsumption_res:                 0
% 7.07/1.50  sim_tautology_del:                      6
% 7.07/1.50  sim_eq_tautology_del:                   2
% 7.07/1.50  sim_eq_res_simp:                        2
% 7.07/1.50  sim_fw_demodulated:                     0
% 7.07/1.50  sim_bw_demodulated:                     4
% 7.07/1.50  sim_light_normalised:                   12
% 7.07/1.50  sim_joinable_taut:                      0
% 7.07/1.50  sim_joinable_simp:                      0
% 7.07/1.50  sim_ac_normalised:                      0
% 7.07/1.50  sim_smt_subsumption:                    0
% 7.07/1.50  
%------------------------------------------------------------------------------

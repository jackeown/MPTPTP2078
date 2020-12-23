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
% DateTime   : Thu Dec  3 12:08:15 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  193 (1165 expanded)
%              Number of clauses        :  112 ( 402 expanded)
%              Number of leaves         :   24 ( 300 expanded)
%              Depth                    :   21
%              Number of atoms          :  812 (7345 expanded)
%              Number of equality atoms :  260 (2199 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,
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

fof(f57,plain,
    ( ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
      | ~ v1_funct_2(sK13,sK11,sK12)
      | ~ v1_funct_1(sK13) )
    & r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f31,f56])).

fof(f101,plain,(
    r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f11,f32])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f90])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f51,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X0)
        & k1_relat_1(sK9(X0,X1,X6)) = X1
        & sK9(X0,X1,X6) = X6
        & v1_funct_1(sK9(X0,X1,X6))
        & v1_relat_1(sK9(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0)
        & k1_relat_1(sK8(X0,X1,X2)) = X1
        & sK8(X0,X1,X2) = X3
        & v1_funct_1(sK8(X0,X1,X2))
        & v1_relat_1(sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
              | sK7(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK7(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK7(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0)
              & k1_relat_1(sK8(X0,X1,X2)) = X1
              & sK7(X0,X1,X2) = sK8(X0,X1,X2)
              & v1_funct_1(sK8(X0,X1,X2))
              & v1_relat_1(sK8(X0,X1,X2)) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X0)
                & k1_relat_1(sK9(X0,X1,X6)) = X1
                & sK9(X0,X1,X6) = X6
                & v1_funct_1(sK9(X0,X1,X6))
                & v1_relat_1(sK9(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f48,f51,f50,f49])).

fof(f81,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK9(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ! [X6,X2,X0,X1] :
      ( sK9(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK10(X0,X1,X2)),X1)
        & r2_hidden(sK10(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK10(X0,X1,X2)),X1)
        & r2_hidden(sK10(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f30,f54])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK10(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f113,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK10(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f98])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK10(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f111,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK10(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f100])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_2(sK13,sK11,sK12)
    | ~ v1_funct_1(sK13) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK9(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK9(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK10(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f112,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK10(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f99])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK10(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f114,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK10(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f97])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f43,f42,f41])).

fof(f66,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
     => ( r2_hidden(sK6(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(sK6(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f45])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9276,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_44,negated_conjecture,
    ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_9255,plain,
    ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_33,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_9259,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK9(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9264,plain,
    ( k1_relat_1(sK9(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12027,plain,
    ( k1_relat_1(sK9(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9259,c_9264])).

cnf(c_21017,plain,
    ( k1_relat_1(sK9(sK12,sK11,sK13)) = sK11 ),
    inference(superposition,[status(thm)],[c_9255,c_12027])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK9(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_9263,plain,
    ( sK9(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11303,plain,
    ( sK9(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9259,c_9263])).

cnf(c_18843,plain,
    ( sK9(sK12,sK11,sK13) = sK13 ),
    inference(superposition,[status(thm)],[c_9255,c_11303])).

cnf(c_21042,plain,
    ( k1_relat_1(sK13) = sK11 ),
    inference(light_normalisation,[status(thm)],[c_21017,c_18843])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_666,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k1_funct_1(X3,sK10(k1_relat_1(X3),X4,X3)),X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | X4 != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_667,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_37,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_671,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_37])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_687,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_671,c_0])).

cnf(c_16,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_43,negated_conjecture,
    ( ~ v1_funct_2(sK13,sK11,sK12)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_695,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK13)
    | sK12 != X2
    | sK11 != X1
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_43])).

cnf(c_696,plain,
    ( ~ v1_partfun1(sK13,sK11)
    | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_858,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK11
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_687,c_696])).

cnf(c_859,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ r2_hidden(k1_funct_1(sK13,sK10(k1_relat_1(sK13),X0,sK13)),X0)
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(sK13)
    | k1_relat_1(sK13) != sK11 ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_8337,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(sK13)
    | sP2_iProver_split
    | k1_relat_1(sK13) != sK11 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_859])).

cnf(c_9250,plain,
    ( k1_relat_1(sK13) != sK11
    | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8337])).

cnf(c_21306,plain,
    ( sK11 != sK11
    | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_21042,c_9250])).

cnf(c_21332,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_21306])).

cnf(c_45,plain,
    ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_149,plain,
    ( r1_tarski(sK13,sK13) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_153,plain,
    ( ~ r1_tarski(sK13,sK13)
    | sK13 = sK13 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK9(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9633,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | v1_funct_1(sK9(X0,X1,sK13)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_9736,plain,
    ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | v1_funct_1(sK9(sK12,sK11,sK13)) ),
    inference(instantiation,[status(thm)],[c_9633])).

cnf(c_9738,plain,
    ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
    | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top
    | v1_funct_1(sK9(sK12,sK11,sK13)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9736])).

cnf(c_9737,plain,
    ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_9740,plain,
    ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9737])).

cnf(c_8350,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_9902,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK9(sK12,sK11,sK13))
    | X0 != sK9(sK12,sK11,sK13) ),
    inference(instantiation,[status(thm)],[c_8350])).

cnf(c_9903,plain,
    ( X0 != sK9(sK12,sK11,sK13)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK9(sK12,sK11,sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9902])).

cnf(c_9905,plain,
    ( sK13 != sK9(sK12,sK11,sK13)
    | v1_funct_1(sK9(sK12,sK11,sK13)) != iProver_top
    | v1_funct_1(sK13) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9903])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK9(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_9638,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | v1_relat_1(sK9(X0,X1,sK13)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_9939,plain,
    ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | v1_relat_1(sK9(sK12,sK11,sK13)) ),
    inference(instantiation,[status(thm)],[c_9638])).

cnf(c_9941,plain,
    ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
    | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top
    | v1_relat_1(sK9(sK12,sK11,sK13)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9939])).

cnf(c_9682,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | sK9(X0,X1,sK13) = sK13 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_9938,plain,
    ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
    | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
    | sK9(sK12,sK11,sK13) = sK13 ),
    inference(instantiation,[status(thm)],[c_9682])).

cnf(c_8349,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_10017,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK9(sK12,sK11,sK13))
    | X0 != sK9(sK12,sK11,sK13) ),
    inference(instantiation,[status(thm)],[c_8349])).

cnf(c_10023,plain,
    ( X0 != sK9(sK12,sK11,sK13)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK9(sK12,sK11,sK13)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10017])).

cnf(c_10025,plain,
    ( sK13 != sK9(sK12,sK11,sK13)
    | v1_relat_1(sK9(sK12,sK11,sK13)) != iProver_top
    | v1_relat_1(sK13) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10023])).

cnf(c_8340,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_10349,plain,
    ( X0 != X1
    | X0 = sK9(sK12,sK11,sK13)
    | sK9(sK12,sK11,sK13) != X1 ),
    inference(instantiation,[status(thm)],[c_8340])).

cnf(c_10350,plain,
    ( sK9(sK12,sK11,sK13) != sK13
    | sK13 = sK9(sK12,sK11,sK13)
    | sK13 != sK13 ),
    inference(instantiation,[status(thm)],[c_10349])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_615,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_616,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_620,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_34])).

cnf(c_903,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK11
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_620,c_696])).

cnf(c_904,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(sK13)
    | v1_xboole_0(k2_relat_1(sK13))
    | k1_relat_1(sK13) != sK11 ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_972,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(sK13)
    | k2_relat_1(sK13) != X1
    | k1_relat_1(sK13) != sK11 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_904])).

cnf(c_973,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ r2_hidden(X0,k2_relat_1(sK13))
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(sK13)
    | k1_relat_1(sK13) != sK11 ),
    inference(unflattening,[status(thm)],[c_972])).

cnf(c_8333,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(sK13)
    | sP0_iProver_split
    | k1_relat_1(sK13) != sK11 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_973])).

cnf(c_9246,plain,
    ( k1_relat_1(sK13) != sK11
    | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8333])).

cnf(c_21303,plain,
    ( sK11 != sK11
    | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_21042,c_9246])).

cnf(c_21351,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_21303])).

cnf(c_38,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK10(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_9256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r2_hidden(sK10(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_21777,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK13),X0))) = iProver_top
    | r2_hidden(sK10(sK11,X0,sK13),sK11) = iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_21042,c_9256])).

cnf(c_21783,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0))) = iProver_top
    | r2_hidden(sK10(sK11,X0,sK13),sK11) = iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21777,c_21042])).

cnf(c_30786,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0))) = iProver_top
    | r2_hidden(sK10(sK11,X0,sK13),sK11) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21783,c_44,c_45,c_149,c_153,c_9738,c_9737,c_9740,c_9905,c_9941,c_9938,c_10025,c_10350])).

cnf(c_40,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK10(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_727,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | r2_hidden(sK10(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK11
    | sK12 != X1
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_43])).

cnf(c_728,plain,
    ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
    | r2_hidden(sK10(k1_relat_1(sK13),sK12,sK13),k1_relat_1(sK13))
    | ~ v1_funct_1(sK13)
    | ~ v1_relat_1(sK13)
    | k1_relat_1(sK13) != sK11 ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_9252,plain,
    ( k1_relat_1(sK13) != sK11
    | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | r2_hidden(sK10(k1_relat_1(sK13),sK12,sK13),k1_relat_1(sK13)) = iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_21308,plain,
    ( sK11 != sK11
    | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | r2_hidden(sK10(sK11,sK12,sK13),sK11) = iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21042,c_9252])).

cnf(c_21319,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | r2_hidden(sK10(sK11,sK12,sK13),sK11) = iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_21308])).

cnf(c_23536,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
    | r2_hidden(sK10(sK11,sK12,sK13),sK11) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21319,c_44,c_45,c_149,c_153,c_9738,c_9737,c_9740,c_9905,c_9941,c_9938,c_10025,c_10350])).

cnf(c_30797,plain,
    ( r2_hidden(sK10(sK11,sK12,sK13),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_30786,c_23536])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_9277,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9258,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_21775,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,k2_relat_1(sK13)))) = iProver_top
    | v1_funct_1(sK13) != iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_21042,c_9258])).

cnf(c_23043,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,k2_relat_1(sK13)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21775,c_44,c_45,c_149,c_153,c_9738,c_9737,c_9740,c_9905,c_9941,c_9938,c_10025,c_10350])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK6(X3,X1,X2),X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_9275,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(sK6(X3,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23049,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | r2_hidden(sK6(X0,sK11,k2_relat_1(sK13)),k2_relat_1(sK13)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23043,c_9275])).

cnf(c_8332,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK13))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_973])).

cnf(c_9247,plain,
    ( r2_hidden(X0,k2_relat_1(sK13)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8332])).

cnf(c_27551,plain,
    ( r2_hidden(X0,sK13) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_23049,c_9247])).

cnf(c_35908,plain,
    ( r2_hidden(X0,k1_relat_1(sK13)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_9277,c_27551])).

cnf(c_35979,plain,
    ( r2_hidden(X0,sK11) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35908,c_21042])).

cnf(c_36288,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_30797,c_35979])).

cnf(c_37719,plain,
    ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21332,c_44,c_45,c_149,c_153,c_9738,c_9737,c_9740,c_9905,c_9941,c_9938,c_10025,c_10350,c_21351,c_36288])).

cnf(c_37725,plain,
    ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
    | r1_tarski(k1_relat_1(sK13),sK11) != iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_9276,c_37719])).

cnf(c_37730,plain,
    ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
    | r1_tarski(sK11,sK11) != iProver_top
    | v1_relat_1(sK13) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_37725,c_21042])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_28585,plain,
    ( r1_tarski(sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_28588,plain,
    ( r1_tarski(sK11,sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28585])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_9265,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12674,plain,
    ( r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9259,c_9265])).

cnf(c_27650,plain,
    ( r1_tarski(k2_relat_1(sK13),sK12) = iProver_top
    | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18843,c_12674])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37730,c_28588,c_27650,c_10350,c_10025,c_9938,c_9941,c_9740,c_9737,c_153,c_149,c_45,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.52/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/1.51  
% 7.52/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.52/1.51  
% 7.52/1.51  ------  iProver source info
% 7.52/1.51  
% 7.52/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.52/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.52/1.51  git: non_committed_changes: false
% 7.52/1.51  git: last_make_outside_of_git: false
% 7.52/1.51  
% 7.52/1.51  ------ 
% 7.52/1.51  
% 7.52/1.51  ------ Input Options
% 7.52/1.51  
% 7.52/1.51  --out_options                           all
% 7.52/1.51  --tptp_safe_out                         true
% 7.52/1.51  --problem_path                          ""
% 7.52/1.51  --include_path                          ""
% 7.52/1.51  --clausifier                            res/vclausify_rel
% 7.52/1.51  --clausifier_options                    --mode clausify
% 7.52/1.51  --stdin                                 false
% 7.52/1.51  --stats_out                             all
% 7.52/1.51  
% 7.52/1.51  ------ General Options
% 7.52/1.51  
% 7.52/1.51  --fof                                   false
% 7.52/1.51  --time_out_real                         305.
% 7.52/1.51  --time_out_virtual                      -1.
% 7.52/1.51  --symbol_type_check                     false
% 7.52/1.51  --clausify_out                          false
% 7.52/1.51  --sig_cnt_out                           false
% 7.52/1.51  --trig_cnt_out                          false
% 7.52/1.51  --trig_cnt_out_tolerance                1.
% 7.52/1.51  --trig_cnt_out_sk_spl                   false
% 7.52/1.51  --abstr_cl_out                          false
% 7.52/1.51  
% 7.52/1.51  ------ Global Options
% 7.52/1.51  
% 7.52/1.51  --schedule                              default
% 7.52/1.51  --add_important_lit                     false
% 7.52/1.51  --prop_solver_per_cl                    1000
% 7.52/1.51  --min_unsat_core                        false
% 7.52/1.51  --soft_assumptions                      false
% 7.52/1.51  --soft_lemma_size                       3
% 7.52/1.51  --prop_impl_unit_size                   0
% 7.52/1.51  --prop_impl_unit                        []
% 7.52/1.51  --share_sel_clauses                     true
% 7.52/1.51  --reset_solvers                         false
% 7.52/1.51  --bc_imp_inh                            [conj_cone]
% 7.52/1.51  --conj_cone_tolerance                   3.
% 7.52/1.51  --extra_neg_conj                        none
% 7.52/1.51  --large_theory_mode                     true
% 7.52/1.51  --prolific_symb_bound                   200
% 7.52/1.51  --lt_threshold                          2000
% 7.52/1.51  --clause_weak_htbl                      true
% 7.52/1.51  --gc_record_bc_elim                     false
% 7.52/1.51  
% 7.52/1.51  ------ Preprocessing Options
% 7.52/1.51  
% 7.52/1.51  --preprocessing_flag                    true
% 7.52/1.51  --time_out_prep_mult                    0.1
% 7.52/1.51  --splitting_mode                        input
% 7.52/1.51  --splitting_grd                         true
% 7.52/1.51  --splitting_cvd                         false
% 7.52/1.51  --splitting_cvd_svl                     false
% 7.52/1.51  --splitting_nvd                         32
% 7.52/1.51  --sub_typing                            true
% 7.52/1.51  --prep_gs_sim                           true
% 7.52/1.51  --prep_unflatten                        true
% 7.52/1.51  --prep_res_sim                          true
% 7.52/1.51  --prep_upred                            true
% 7.52/1.51  --prep_sem_filter                       exhaustive
% 7.52/1.51  --prep_sem_filter_out                   false
% 7.52/1.51  --pred_elim                             true
% 7.52/1.51  --res_sim_input                         true
% 7.52/1.51  --eq_ax_congr_red                       true
% 7.52/1.51  --pure_diseq_elim                       true
% 7.52/1.51  --brand_transform                       false
% 7.52/1.51  --non_eq_to_eq                          false
% 7.52/1.51  --prep_def_merge                        true
% 7.52/1.51  --prep_def_merge_prop_impl              false
% 7.52/1.51  --prep_def_merge_mbd                    true
% 7.52/1.51  --prep_def_merge_tr_red                 false
% 7.52/1.51  --prep_def_merge_tr_cl                  false
% 7.52/1.51  --smt_preprocessing                     true
% 7.52/1.51  --smt_ac_axioms                         fast
% 7.52/1.51  --preprocessed_out                      false
% 7.52/1.51  --preprocessed_stats                    false
% 7.52/1.51  
% 7.52/1.51  ------ Abstraction refinement Options
% 7.52/1.51  
% 7.52/1.51  --abstr_ref                             []
% 7.52/1.51  --abstr_ref_prep                        false
% 7.52/1.51  --abstr_ref_until_sat                   false
% 7.52/1.51  --abstr_ref_sig_restrict                funpre
% 7.52/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.52/1.51  --abstr_ref_under                       []
% 7.52/1.51  
% 7.52/1.51  ------ SAT Options
% 7.52/1.51  
% 7.52/1.51  --sat_mode                              false
% 7.52/1.51  --sat_fm_restart_options                ""
% 7.52/1.51  --sat_gr_def                            false
% 7.52/1.51  --sat_epr_types                         true
% 7.52/1.51  --sat_non_cyclic_types                  false
% 7.52/1.51  --sat_finite_models                     false
% 7.52/1.51  --sat_fm_lemmas                         false
% 7.52/1.51  --sat_fm_prep                           false
% 7.52/1.51  --sat_fm_uc_incr                        true
% 7.52/1.51  --sat_out_model                         small
% 7.52/1.51  --sat_out_clauses                       false
% 7.52/1.51  
% 7.52/1.51  ------ QBF Options
% 7.52/1.51  
% 7.52/1.51  --qbf_mode                              false
% 7.52/1.51  --qbf_elim_univ                         false
% 7.52/1.51  --qbf_dom_inst                          none
% 7.52/1.51  --qbf_dom_pre_inst                      false
% 7.52/1.51  --qbf_sk_in                             false
% 7.52/1.51  --qbf_pred_elim                         true
% 7.52/1.51  --qbf_split                             512
% 7.52/1.51  
% 7.52/1.51  ------ BMC1 Options
% 7.52/1.51  
% 7.52/1.51  --bmc1_incremental                      false
% 7.52/1.51  --bmc1_axioms                           reachable_all
% 7.52/1.51  --bmc1_min_bound                        0
% 7.52/1.51  --bmc1_max_bound                        -1
% 7.52/1.51  --bmc1_max_bound_default                -1
% 7.52/1.51  --bmc1_symbol_reachability              true
% 7.52/1.51  --bmc1_property_lemmas                  false
% 7.52/1.51  --bmc1_k_induction                      false
% 7.52/1.51  --bmc1_non_equiv_states                 false
% 7.52/1.51  --bmc1_deadlock                         false
% 7.52/1.51  --bmc1_ucm                              false
% 7.52/1.51  --bmc1_add_unsat_core                   none
% 7.52/1.51  --bmc1_unsat_core_children              false
% 7.52/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.52/1.51  --bmc1_out_stat                         full
% 7.52/1.51  --bmc1_ground_init                      false
% 7.52/1.51  --bmc1_pre_inst_next_state              false
% 7.52/1.51  --bmc1_pre_inst_state                   false
% 7.52/1.51  --bmc1_pre_inst_reach_state             false
% 7.52/1.51  --bmc1_out_unsat_core                   false
% 7.52/1.51  --bmc1_aig_witness_out                  false
% 7.52/1.51  --bmc1_verbose                          false
% 7.52/1.51  --bmc1_dump_clauses_tptp                false
% 7.52/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.52/1.51  --bmc1_dump_file                        -
% 7.52/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.52/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.52/1.51  --bmc1_ucm_extend_mode                  1
% 7.52/1.51  --bmc1_ucm_init_mode                    2
% 7.52/1.51  --bmc1_ucm_cone_mode                    none
% 7.52/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.52/1.51  --bmc1_ucm_relax_model                  4
% 7.52/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.52/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.52/1.51  --bmc1_ucm_layered_model                none
% 7.52/1.51  --bmc1_ucm_max_lemma_size               10
% 7.52/1.51  
% 7.52/1.51  ------ AIG Options
% 7.52/1.51  
% 7.52/1.51  --aig_mode                              false
% 7.52/1.51  
% 7.52/1.51  ------ Instantiation Options
% 7.52/1.51  
% 7.52/1.51  --instantiation_flag                    true
% 7.52/1.51  --inst_sos_flag                         false
% 7.52/1.51  --inst_sos_phase                        true
% 7.52/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.52/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.52/1.51  --inst_lit_sel_side                     num_symb
% 7.52/1.51  --inst_solver_per_active                1400
% 7.52/1.51  --inst_solver_calls_frac                1.
% 7.52/1.51  --inst_passive_queue_type               priority_queues
% 7.52/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.52/1.51  --inst_passive_queues_freq              [25;2]
% 7.52/1.51  --inst_dismatching                      true
% 7.52/1.51  --inst_eager_unprocessed_to_passive     true
% 7.52/1.51  --inst_prop_sim_given                   true
% 7.52/1.51  --inst_prop_sim_new                     false
% 7.52/1.51  --inst_subs_new                         false
% 7.52/1.51  --inst_eq_res_simp                      false
% 7.52/1.51  --inst_subs_given                       false
% 7.52/1.51  --inst_orphan_elimination               true
% 7.52/1.51  --inst_learning_loop_flag               true
% 7.52/1.51  --inst_learning_start                   3000
% 7.52/1.51  --inst_learning_factor                  2
% 7.52/1.51  --inst_start_prop_sim_after_learn       3
% 7.52/1.51  --inst_sel_renew                        solver
% 7.52/1.51  --inst_lit_activity_flag                true
% 7.52/1.51  --inst_restr_to_given                   false
% 7.52/1.51  --inst_activity_threshold               500
% 7.52/1.51  --inst_out_proof                        true
% 7.52/1.51  
% 7.52/1.51  ------ Resolution Options
% 7.52/1.51  
% 7.52/1.51  --resolution_flag                       true
% 7.52/1.51  --res_lit_sel                           adaptive
% 7.52/1.51  --res_lit_sel_side                      none
% 7.52/1.51  --res_ordering                          kbo
% 7.52/1.51  --res_to_prop_solver                    active
% 7.52/1.51  --res_prop_simpl_new                    false
% 7.52/1.51  --res_prop_simpl_given                  true
% 7.52/1.51  --res_passive_queue_type                priority_queues
% 7.52/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.52/1.51  --res_passive_queues_freq               [15;5]
% 7.52/1.51  --res_forward_subs                      full
% 7.52/1.51  --res_backward_subs                     full
% 7.52/1.51  --res_forward_subs_resolution           true
% 7.52/1.51  --res_backward_subs_resolution          true
% 7.52/1.51  --res_orphan_elimination                true
% 7.52/1.51  --res_time_limit                        2.
% 7.52/1.51  --res_out_proof                         true
% 7.52/1.51  
% 7.52/1.51  ------ Superposition Options
% 7.52/1.51  
% 7.52/1.51  --superposition_flag                    true
% 7.52/1.51  --sup_passive_queue_type                priority_queues
% 7.52/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.52/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.52/1.51  --demod_completeness_check              fast
% 7.52/1.51  --demod_use_ground                      true
% 7.52/1.51  --sup_to_prop_solver                    passive
% 7.52/1.51  --sup_prop_simpl_new                    true
% 7.52/1.51  --sup_prop_simpl_given                  true
% 7.52/1.51  --sup_fun_splitting                     false
% 7.52/1.51  --sup_smt_interval                      50000
% 7.52/1.51  
% 7.52/1.51  ------ Superposition Simplification Setup
% 7.52/1.51  
% 7.52/1.51  --sup_indices_passive                   []
% 7.52/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.52/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.51  --sup_full_bw                           [BwDemod]
% 7.52/1.51  --sup_immed_triv                        [TrivRules]
% 7.52/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.51  --sup_immed_bw_main                     []
% 7.52/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.52/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.52/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.52/1.51  
% 7.52/1.51  ------ Combination Options
% 7.52/1.51  
% 7.52/1.51  --comb_res_mult                         3
% 7.52/1.51  --comb_sup_mult                         2
% 7.52/1.51  --comb_inst_mult                        10
% 7.52/1.51  
% 7.52/1.51  ------ Debug Options
% 7.52/1.51  
% 7.52/1.51  --dbg_backtrace                         false
% 7.52/1.51  --dbg_dump_prop_clauses                 false
% 7.52/1.51  --dbg_dump_prop_clauses_file            -
% 7.52/1.51  --dbg_out_stat                          false
% 7.52/1.51  ------ Parsing...
% 7.52/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.52/1.51  
% 7.52/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.52/1.51  
% 7.52/1.51  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.52/1.51  
% 7.52/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.52/1.51  ------ Proving...
% 7.52/1.51  ------ Problem Properties 
% 7.52/1.51  
% 7.52/1.51  
% 7.52/1.51  clauses                                 40
% 7.52/1.51  conjectures                             1
% 7.52/1.51  EPR                                     3
% 7.52/1.51  Horn                                    32
% 7.52/1.51  unary                                   4
% 7.52/1.51  binary                                  8
% 7.52/1.51  lits                                    122
% 7.52/1.51  lits eq                                 17
% 7.52/1.51  fd_pure                                 0
% 7.52/1.51  fd_pseudo                               0
% 7.52/1.51  fd_cond                                 1
% 7.52/1.51  fd_pseudo_cond                          4
% 7.52/1.51  AC symbols                              0
% 7.52/1.51  
% 7.52/1.51  ------ Schedule dynamic 5 is on 
% 7.52/1.51  
% 7.52/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.52/1.51  
% 7.52/1.51  
% 7.52/1.51  ------ 
% 7.52/1.51  Current options:
% 7.52/1.51  ------ 
% 7.52/1.51  
% 7.52/1.51  ------ Input Options
% 7.52/1.51  
% 7.52/1.51  --out_options                           all
% 7.52/1.51  --tptp_safe_out                         true
% 7.52/1.51  --problem_path                          ""
% 7.52/1.51  --include_path                          ""
% 7.52/1.51  --clausifier                            res/vclausify_rel
% 7.52/1.51  --clausifier_options                    --mode clausify
% 7.52/1.51  --stdin                                 false
% 7.52/1.51  --stats_out                             all
% 7.52/1.51  
% 7.52/1.51  ------ General Options
% 7.52/1.51  
% 7.52/1.51  --fof                                   false
% 7.52/1.51  --time_out_real                         305.
% 7.52/1.51  --time_out_virtual                      -1.
% 7.52/1.51  --symbol_type_check                     false
% 7.52/1.51  --clausify_out                          false
% 7.52/1.51  --sig_cnt_out                           false
% 7.52/1.51  --trig_cnt_out                          false
% 7.52/1.51  --trig_cnt_out_tolerance                1.
% 7.52/1.51  --trig_cnt_out_sk_spl                   false
% 7.52/1.51  --abstr_cl_out                          false
% 7.52/1.51  
% 7.52/1.51  ------ Global Options
% 7.52/1.51  
% 7.52/1.51  --schedule                              default
% 7.52/1.51  --add_important_lit                     false
% 7.52/1.51  --prop_solver_per_cl                    1000
% 7.52/1.51  --min_unsat_core                        false
% 7.52/1.51  --soft_assumptions                      false
% 7.52/1.51  --soft_lemma_size                       3
% 7.52/1.51  --prop_impl_unit_size                   0
% 7.52/1.51  --prop_impl_unit                        []
% 7.52/1.51  --share_sel_clauses                     true
% 7.52/1.51  --reset_solvers                         false
% 7.52/1.51  --bc_imp_inh                            [conj_cone]
% 7.52/1.51  --conj_cone_tolerance                   3.
% 7.52/1.51  --extra_neg_conj                        none
% 7.52/1.51  --large_theory_mode                     true
% 7.52/1.51  --prolific_symb_bound                   200
% 7.52/1.51  --lt_threshold                          2000
% 7.52/1.51  --clause_weak_htbl                      true
% 7.52/1.51  --gc_record_bc_elim                     false
% 7.52/1.51  
% 7.52/1.51  ------ Preprocessing Options
% 7.52/1.51  
% 7.52/1.51  --preprocessing_flag                    true
% 7.52/1.51  --time_out_prep_mult                    0.1
% 7.52/1.51  --splitting_mode                        input
% 7.52/1.51  --splitting_grd                         true
% 7.52/1.51  --splitting_cvd                         false
% 7.52/1.51  --splitting_cvd_svl                     false
% 7.52/1.51  --splitting_nvd                         32
% 7.52/1.51  --sub_typing                            true
% 7.52/1.51  --prep_gs_sim                           true
% 7.52/1.51  --prep_unflatten                        true
% 7.52/1.51  --prep_res_sim                          true
% 7.52/1.51  --prep_upred                            true
% 7.52/1.51  --prep_sem_filter                       exhaustive
% 7.52/1.51  --prep_sem_filter_out                   false
% 7.52/1.51  --pred_elim                             true
% 7.52/1.51  --res_sim_input                         true
% 7.52/1.51  --eq_ax_congr_red                       true
% 7.52/1.51  --pure_diseq_elim                       true
% 7.52/1.51  --brand_transform                       false
% 7.52/1.51  --non_eq_to_eq                          false
% 7.52/1.51  --prep_def_merge                        true
% 7.52/1.51  --prep_def_merge_prop_impl              false
% 7.52/1.51  --prep_def_merge_mbd                    true
% 7.52/1.51  --prep_def_merge_tr_red                 false
% 7.52/1.51  --prep_def_merge_tr_cl                  false
% 7.52/1.51  --smt_preprocessing                     true
% 7.52/1.51  --smt_ac_axioms                         fast
% 7.52/1.51  --preprocessed_out                      false
% 7.52/1.51  --preprocessed_stats                    false
% 7.52/1.51  
% 7.52/1.51  ------ Abstraction refinement Options
% 7.52/1.51  
% 7.52/1.51  --abstr_ref                             []
% 7.52/1.51  --abstr_ref_prep                        false
% 7.52/1.51  --abstr_ref_until_sat                   false
% 7.52/1.51  --abstr_ref_sig_restrict                funpre
% 7.52/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.52/1.51  --abstr_ref_under                       []
% 7.52/1.51  
% 7.52/1.51  ------ SAT Options
% 7.52/1.51  
% 7.52/1.51  --sat_mode                              false
% 7.52/1.51  --sat_fm_restart_options                ""
% 7.52/1.51  --sat_gr_def                            false
% 7.52/1.51  --sat_epr_types                         true
% 7.52/1.51  --sat_non_cyclic_types                  false
% 7.52/1.51  --sat_finite_models                     false
% 7.52/1.51  --sat_fm_lemmas                         false
% 7.52/1.51  --sat_fm_prep                           false
% 7.52/1.51  --sat_fm_uc_incr                        true
% 7.52/1.51  --sat_out_model                         small
% 7.52/1.51  --sat_out_clauses                       false
% 7.52/1.51  
% 7.52/1.51  ------ QBF Options
% 7.52/1.51  
% 7.52/1.51  --qbf_mode                              false
% 7.52/1.51  --qbf_elim_univ                         false
% 7.52/1.51  --qbf_dom_inst                          none
% 7.52/1.51  --qbf_dom_pre_inst                      false
% 7.52/1.51  --qbf_sk_in                             false
% 7.52/1.51  --qbf_pred_elim                         true
% 7.52/1.51  --qbf_split                             512
% 7.52/1.51  
% 7.52/1.51  ------ BMC1 Options
% 7.52/1.51  
% 7.52/1.51  --bmc1_incremental                      false
% 7.52/1.51  --bmc1_axioms                           reachable_all
% 7.52/1.51  --bmc1_min_bound                        0
% 7.52/1.51  --bmc1_max_bound                        -1
% 7.52/1.51  --bmc1_max_bound_default                -1
% 7.52/1.51  --bmc1_symbol_reachability              true
% 7.52/1.51  --bmc1_property_lemmas                  false
% 7.52/1.51  --bmc1_k_induction                      false
% 7.52/1.51  --bmc1_non_equiv_states                 false
% 7.52/1.51  --bmc1_deadlock                         false
% 7.52/1.51  --bmc1_ucm                              false
% 7.52/1.51  --bmc1_add_unsat_core                   none
% 7.52/1.51  --bmc1_unsat_core_children              false
% 7.52/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.52/1.51  --bmc1_out_stat                         full
% 7.52/1.51  --bmc1_ground_init                      false
% 7.52/1.51  --bmc1_pre_inst_next_state              false
% 7.52/1.51  --bmc1_pre_inst_state                   false
% 7.52/1.51  --bmc1_pre_inst_reach_state             false
% 7.52/1.51  --bmc1_out_unsat_core                   false
% 7.52/1.51  --bmc1_aig_witness_out                  false
% 7.52/1.51  --bmc1_verbose                          false
% 7.52/1.51  --bmc1_dump_clauses_tptp                false
% 7.52/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.52/1.51  --bmc1_dump_file                        -
% 7.52/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.52/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.52/1.51  --bmc1_ucm_extend_mode                  1
% 7.52/1.51  --bmc1_ucm_init_mode                    2
% 7.52/1.51  --bmc1_ucm_cone_mode                    none
% 7.52/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.52/1.51  --bmc1_ucm_relax_model                  4
% 7.52/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.52/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.52/1.51  --bmc1_ucm_layered_model                none
% 7.52/1.51  --bmc1_ucm_max_lemma_size               10
% 7.52/1.51  
% 7.52/1.51  ------ AIG Options
% 7.52/1.51  
% 7.52/1.51  --aig_mode                              false
% 7.52/1.51  
% 7.52/1.51  ------ Instantiation Options
% 7.52/1.51  
% 7.52/1.51  --instantiation_flag                    true
% 7.52/1.51  --inst_sos_flag                         false
% 7.52/1.51  --inst_sos_phase                        true
% 7.52/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.52/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.52/1.51  --inst_lit_sel_side                     none
% 7.52/1.51  --inst_solver_per_active                1400
% 7.52/1.51  --inst_solver_calls_frac                1.
% 7.52/1.51  --inst_passive_queue_type               priority_queues
% 7.52/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.52/1.51  --inst_passive_queues_freq              [25;2]
% 7.52/1.51  --inst_dismatching                      true
% 7.52/1.51  --inst_eager_unprocessed_to_passive     true
% 7.52/1.51  --inst_prop_sim_given                   true
% 7.52/1.51  --inst_prop_sim_new                     false
% 7.52/1.51  --inst_subs_new                         false
% 7.52/1.51  --inst_eq_res_simp                      false
% 7.52/1.51  --inst_subs_given                       false
% 7.52/1.51  --inst_orphan_elimination               true
% 7.52/1.51  --inst_learning_loop_flag               true
% 7.52/1.51  --inst_learning_start                   3000
% 7.52/1.51  --inst_learning_factor                  2
% 7.52/1.51  --inst_start_prop_sim_after_learn       3
% 7.52/1.51  --inst_sel_renew                        solver
% 7.52/1.51  --inst_lit_activity_flag                true
% 7.52/1.51  --inst_restr_to_given                   false
% 7.52/1.51  --inst_activity_threshold               500
% 7.52/1.51  --inst_out_proof                        true
% 7.52/1.51  
% 7.52/1.51  ------ Resolution Options
% 7.52/1.51  
% 7.52/1.51  --resolution_flag                       false
% 7.52/1.51  --res_lit_sel                           adaptive
% 7.52/1.51  --res_lit_sel_side                      none
% 7.52/1.51  --res_ordering                          kbo
% 7.52/1.51  --res_to_prop_solver                    active
% 7.52/1.51  --res_prop_simpl_new                    false
% 7.52/1.51  --res_prop_simpl_given                  true
% 7.52/1.51  --res_passive_queue_type                priority_queues
% 7.52/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.52/1.51  --res_passive_queues_freq               [15;5]
% 7.52/1.51  --res_forward_subs                      full
% 7.52/1.51  --res_backward_subs                     full
% 7.52/1.51  --res_forward_subs_resolution           true
% 7.52/1.51  --res_backward_subs_resolution          true
% 7.52/1.51  --res_orphan_elimination                true
% 7.52/1.51  --res_time_limit                        2.
% 7.52/1.51  --res_out_proof                         true
% 7.52/1.51  
% 7.52/1.51  ------ Superposition Options
% 7.52/1.51  
% 7.52/1.51  --superposition_flag                    true
% 7.52/1.51  --sup_passive_queue_type                priority_queues
% 7.52/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.52/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.52/1.51  --demod_completeness_check              fast
% 7.52/1.51  --demod_use_ground                      true
% 7.52/1.51  --sup_to_prop_solver                    passive
% 7.52/1.51  --sup_prop_simpl_new                    true
% 7.52/1.51  --sup_prop_simpl_given                  true
% 7.52/1.51  --sup_fun_splitting                     false
% 7.52/1.51  --sup_smt_interval                      50000
% 7.52/1.51  
% 7.52/1.51  ------ Superposition Simplification Setup
% 7.52/1.51  
% 7.52/1.51  --sup_indices_passive                   []
% 7.52/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.52/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.51  --sup_full_bw                           [BwDemod]
% 7.52/1.51  --sup_immed_triv                        [TrivRules]
% 7.52/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.51  --sup_immed_bw_main                     []
% 7.52/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.52/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.52/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.52/1.51  
% 7.52/1.51  ------ Combination Options
% 7.52/1.51  
% 7.52/1.51  --comb_res_mult                         3
% 7.52/1.51  --comb_sup_mult                         2
% 7.52/1.51  --comb_inst_mult                        10
% 7.52/1.51  
% 7.52/1.51  ------ Debug Options
% 7.52/1.51  
% 7.52/1.51  --dbg_backtrace                         false
% 7.52/1.51  --dbg_dump_prop_clauses                 false
% 7.52/1.51  --dbg_dump_prop_clauses_file            -
% 7.52/1.51  --dbg_out_stat                          false
% 7.52/1.51  
% 7.52/1.51  
% 7.52/1.51  
% 7.52/1.51  
% 7.52/1.51  ------ Proving...
% 7.52/1.51  
% 7.52/1.51  
% 7.52/1.51  % SZS status Theorem for theBenchmark.p
% 7.52/1.51  
% 7.52/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.52/1.51  
% 7.52/1.51  fof(f7,axiom,(
% 7.52/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f19,plain,(
% 7.52/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.52/1.51    inference(ennf_transformation,[],[f7])).
% 7.52/1.51  
% 7.52/1.51  fof(f20,plain,(
% 7.52/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.52/1.51    inference(flattening,[],[f19])).
% 7.52/1.51  
% 7.52/1.51  fof(f70,plain,(
% 7.52/1.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f20])).
% 7.52/1.51  
% 7.52/1.51  fof(f14,conjecture,(
% 7.52/1.51    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f15,negated_conjecture,(
% 7.52/1.51    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.52/1.51    inference(negated_conjecture,[],[f14])).
% 7.52/1.51  
% 7.52/1.51  fof(f31,plain,(
% 7.52/1.51    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 7.52/1.51    inference(ennf_transformation,[],[f15])).
% 7.52/1.51  
% 7.52/1.51  fof(f56,plain,(
% 7.52/1.51    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) | ~v1_funct_2(sK13,sK11,sK12) | ~v1_funct_1(sK13)) & r2_hidden(sK13,k1_funct_2(sK11,sK12)))),
% 7.52/1.51    introduced(choice_axiom,[])).
% 7.52/1.51  
% 7.52/1.51  fof(f57,plain,(
% 7.52/1.51    (~m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) | ~v1_funct_2(sK13,sK11,sK12) | ~v1_funct_1(sK13)) & r2_hidden(sK13,k1_funct_2(sK11,sK12))),
% 7.52/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f31,f56])).
% 7.52/1.51  
% 7.52/1.51  fof(f101,plain,(
% 7.52/1.51    r2_hidden(sK13,k1_funct_2(sK11,sK12))),
% 7.52/1.51    inference(cnf_transformation,[],[f57])).
% 7.52/1.51  
% 7.52/1.51  fof(f11,axiom,(
% 7.52/1.51    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f32,plain,(
% 7.52/1.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.52/1.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.52/1.51  
% 7.52/1.51  fof(f33,plain,(
% 7.52/1.51    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 7.52/1.51    inference(definition_folding,[],[f11,f32])).
% 7.52/1.51  
% 7.52/1.51  fof(f53,plain,(
% 7.52/1.51    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 7.52/1.51    inference(nnf_transformation,[],[f33])).
% 7.52/1.51  
% 7.52/1.51  fof(f90,plain,(
% 7.52/1.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 7.52/1.51    inference(cnf_transformation,[],[f53])).
% 7.52/1.51  
% 7.52/1.51  fof(f110,plain,(
% 7.52/1.51    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 7.52/1.51    inference(equality_resolution,[],[f90])).
% 7.52/1.51  
% 7.52/1.51  fof(f47,plain,(
% 7.52/1.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 7.52/1.51    inference(nnf_transformation,[],[f32])).
% 7.52/1.51  
% 7.52/1.51  fof(f48,plain,(
% 7.52/1.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.52/1.51    inference(rectify,[],[f47])).
% 7.52/1.51  
% 7.52/1.51  fof(f51,plain,(
% 7.52/1.51    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X0) & k1_relat_1(sK9(X0,X1,X6)) = X1 & sK9(X0,X1,X6) = X6 & v1_funct_1(sK9(X0,X1,X6)) & v1_relat_1(sK9(X0,X1,X6))))),
% 7.52/1.51    introduced(choice_axiom,[])).
% 7.52/1.51  
% 7.52/1.51  fof(f50,plain,(
% 7.52/1.51    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0) & k1_relat_1(sK8(X0,X1,X2)) = X1 & sK8(X0,X1,X2) = X3 & v1_funct_1(sK8(X0,X1,X2)) & v1_relat_1(sK8(X0,X1,X2))))) )),
% 7.52/1.51    introduced(choice_axiom,[])).
% 7.52/1.51  
% 7.52/1.51  fof(f49,plain,(
% 7.52/1.51    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK7(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK7(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 7.52/1.51    introduced(choice_axiom,[])).
% 7.52/1.51  
% 7.52/1.51  fof(f52,plain,(
% 7.52/1.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK7(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0) & k1_relat_1(sK8(X0,X1,X2)) = X1 & sK7(X0,X1,X2) = sK8(X0,X1,X2) & v1_funct_1(sK8(X0,X1,X2)) & v1_relat_1(sK8(X0,X1,X2))) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X0) & k1_relat_1(sK9(X0,X1,X6)) = X1 & sK9(X0,X1,X6) = X6 & v1_funct_1(sK9(X0,X1,X6)) & v1_relat_1(sK9(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.52/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f48,f51,f50,f49])).
% 7.52/1.51  
% 7.52/1.51  fof(f81,plain,(
% 7.52/1.51    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK9(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f52])).
% 7.52/1.51  
% 7.52/1.51  fof(f80,plain,(
% 7.52/1.51    ( ! [X6,X2,X0,X1] : (sK9(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f52])).
% 7.52/1.51  
% 7.52/1.51  fof(f10,axiom,(
% 7.52/1.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f25,plain,(
% 7.52/1.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.52/1.51    inference(ennf_transformation,[],[f10])).
% 7.52/1.51  
% 7.52/1.51  fof(f26,plain,(
% 7.52/1.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.52/1.51    inference(flattening,[],[f25])).
% 7.52/1.51  
% 7.52/1.51  fof(f77,plain,(
% 7.52/1.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f26])).
% 7.52/1.51  
% 7.52/1.51  fof(f13,axiom,(
% 7.52/1.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f29,plain,(
% 7.52/1.51    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.52/1.51    inference(ennf_transformation,[],[f13])).
% 7.52/1.51  
% 7.52/1.51  fof(f30,plain,(
% 7.52/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.52/1.51    inference(flattening,[],[f29])).
% 7.52/1.51  
% 7.52/1.51  fof(f54,plain,(
% 7.52/1.51    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK10(X0,X1,X2)),X1) & r2_hidden(sK10(X0,X1,X2),X0)))),
% 7.52/1.51    introduced(choice_axiom,[])).
% 7.52/1.51  
% 7.52/1.51  fof(f55,plain,(
% 7.52/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK10(X0,X1,X2)),X1) & r2_hidden(sK10(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.52/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f30,f54])).
% 7.52/1.51  
% 7.52/1.51  fof(f98,plain,(
% 7.52/1.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK10(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f55])).
% 7.52/1.51  
% 7.52/1.51  fof(f113,plain,(
% 7.52/1.51    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK10(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.52/1.51    inference(equality_resolution,[],[f98])).
% 7.52/1.51  
% 7.52/1.51  fof(f100,plain,(
% 7.52/1.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK10(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f55])).
% 7.52/1.51  
% 7.52/1.51  fof(f111,plain,(
% 7.52/1.51    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK10(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.52/1.51    inference(equality_resolution,[],[f100])).
% 7.52/1.51  
% 7.52/1.51  fof(f1,axiom,(
% 7.52/1.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f16,plain,(
% 7.52/1.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 7.52/1.51    inference(unused_predicate_definition_removal,[],[f1])).
% 7.52/1.51  
% 7.52/1.51  fof(f17,plain,(
% 7.52/1.51    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 7.52/1.51    inference(ennf_transformation,[],[f16])).
% 7.52/1.51  
% 7.52/1.51  fof(f58,plain,(
% 7.52/1.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f17])).
% 7.52/1.51  
% 7.52/1.51  fof(f9,axiom,(
% 7.52/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f23,plain,(
% 7.52/1.51    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.52/1.51    inference(ennf_transformation,[],[f9])).
% 7.52/1.51  
% 7.52/1.51  fof(f24,plain,(
% 7.52/1.51    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.52/1.51    inference(flattening,[],[f23])).
% 7.52/1.51  
% 7.52/1.51  fof(f75,plain,(
% 7.52/1.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.52/1.51    inference(cnf_transformation,[],[f24])).
% 7.52/1.51  
% 7.52/1.51  fof(f102,plain,(
% 7.52/1.51    ~m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) | ~v1_funct_2(sK13,sK11,sK12) | ~v1_funct_1(sK13)),
% 7.52/1.51    inference(cnf_transformation,[],[f57])).
% 7.52/1.51  
% 7.52/1.51  fof(f4,axiom,(
% 7.52/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f36,plain,(
% 7.52/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.52/1.51    inference(nnf_transformation,[],[f4])).
% 7.52/1.51  
% 7.52/1.51  fof(f37,plain,(
% 7.52/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.52/1.51    inference(flattening,[],[f36])).
% 7.52/1.51  
% 7.52/1.51  fof(f61,plain,(
% 7.52/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.52/1.51    inference(cnf_transformation,[],[f37])).
% 7.52/1.51  
% 7.52/1.51  fof(f104,plain,(
% 7.52/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.52/1.51    inference(equality_resolution,[],[f61])).
% 7.52/1.51  
% 7.52/1.51  fof(f63,plain,(
% 7.52/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f37])).
% 7.52/1.51  
% 7.52/1.51  fof(f79,plain,(
% 7.52/1.51    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK9(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f52])).
% 7.52/1.51  
% 7.52/1.51  fof(f78,plain,(
% 7.52/1.51    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK9(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f52])).
% 7.52/1.51  
% 7.52/1.51  fof(f12,axiom,(
% 7.52/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f27,plain,(
% 7.52/1.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.52/1.51    inference(ennf_transformation,[],[f12])).
% 7.52/1.51  
% 7.52/1.51  fof(f28,plain,(
% 7.52/1.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.52/1.51    inference(flattening,[],[f27])).
% 7.52/1.51  
% 7.52/1.51  fof(f93,plain,(
% 7.52/1.51    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f28])).
% 7.52/1.51  
% 7.52/1.51  fof(f94,plain,(
% 7.52/1.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f28])).
% 7.52/1.51  
% 7.52/1.51  fof(f99,plain,(
% 7.52/1.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK10(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f55])).
% 7.52/1.51  
% 7.52/1.51  fof(f112,plain,(
% 7.52/1.51    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK10(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.52/1.51    inference(equality_resolution,[],[f99])).
% 7.52/1.51  
% 7.52/1.51  fof(f97,plain,(
% 7.52/1.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK10(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f55])).
% 7.52/1.51  
% 7.52/1.51  fof(f114,plain,(
% 7.52/1.51    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK10(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.52/1.51    inference(equality_resolution,[],[f97])).
% 7.52/1.51  
% 7.52/1.51  fof(f6,axiom,(
% 7.52/1.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f39,plain,(
% 7.52/1.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 7.52/1.51    inference(nnf_transformation,[],[f6])).
% 7.52/1.51  
% 7.52/1.51  fof(f40,plain,(
% 7.52/1.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.52/1.51    inference(rectify,[],[f39])).
% 7.52/1.51  
% 7.52/1.51  fof(f43,plain,(
% 7.52/1.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 7.52/1.51    introduced(choice_axiom,[])).
% 7.52/1.51  
% 7.52/1.51  fof(f42,plain,(
% 7.52/1.51    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 7.52/1.51    introduced(choice_axiom,[])).
% 7.52/1.51  
% 7.52/1.51  fof(f41,plain,(
% 7.52/1.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.52/1.51    introduced(choice_axiom,[])).
% 7.52/1.51  
% 7.52/1.51  fof(f44,plain,(
% 7.52/1.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.52/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f43,f42,f41])).
% 7.52/1.51  
% 7.52/1.51  fof(f66,plain,(
% 7.52/1.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 7.52/1.51    inference(cnf_transformation,[],[f44])).
% 7.52/1.51  
% 7.52/1.51  fof(f106,plain,(
% 7.52/1.51    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 7.52/1.51    inference(equality_resolution,[],[f66])).
% 7.52/1.51  
% 7.52/1.51  fof(f8,axiom,(
% 7.52/1.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 7.52/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.52/1.51  
% 7.52/1.51  fof(f21,plain,(
% 7.52/1.51    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.52/1.51    inference(ennf_transformation,[],[f8])).
% 7.52/1.51  
% 7.52/1.51  fof(f22,plain,(
% 7.52/1.51    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.52/1.51    inference(flattening,[],[f21])).
% 7.52/1.51  
% 7.52/1.51  fof(f45,plain,(
% 7.52/1.51    ! [X2,X1,X0] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) => (r2_hidden(sK6(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0))),
% 7.52/1.51    introduced(choice_axiom,[])).
% 7.52/1.51  
% 7.52/1.51  fof(f46,plain,(
% 7.52/1.51    ! [X0,X1,X2,X3] : ((r2_hidden(sK6(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.52/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f45])).
% 7.52/1.51  
% 7.52/1.51  fof(f73,plain,(
% 7.52/1.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 7.52/1.51    inference(cnf_transformation,[],[f46])).
% 7.52/1.51  
% 7.52/1.51  fof(f62,plain,(
% 7.52/1.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.52/1.51    inference(cnf_transformation,[],[f37])).
% 7.52/1.51  
% 7.52/1.51  fof(f103,plain,(
% 7.52/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.52/1.51    inference(equality_resolution,[],[f62])).
% 7.52/1.51  
% 7.52/1.51  fof(f82,plain,(
% 7.52/1.51    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK9(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.52/1.51    inference(cnf_transformation,[],[f52])).
% 7.52/1.51  
% 7.52/1.51  cnf(c_12,plain,
% 7.52/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.51      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.52/1.51      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.52/1.51      | ~ v1_relat_1(X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9276,plain,
% 7.52/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.52/1.51      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.52/1.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.52/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_44,negated_conjecture,
% 7.52/1.51      ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) ),
% 7.52/1.51      inference(cnf_transformation,[],[f101]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9255,plain,
% 7.52/1.51      ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_33,plain,
% 7.52/1.51      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 7.52/1.51      inference(cnf_transformation,[],[f110]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9259,plain,
% 7.52/1.51      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_28,plain,
% 7.52/1.51      ( ~ sP0(X0,X1,X2)
% 7.52/1.51      | ~ r2_hidden(X3,X2)
% 7.52/1.51      | k1_relat_1(sK9(X0,X1,X3)) = X1 ),
% 7.52/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9264,plain,
% 7.52/1.51      ( k1_relat_1(sK9(X0,X1,X2)) = X1
% 7.52/1.51      | sP0(X0,X1,X3) != iProver_top
% 7.52/1.51      | r2_hidden(X2,X3) != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_12027,plain,
% 7.52/1.51      ( k1_relat_1(sK9(X0,X1,X2)) = X1
% 7.52/1.51      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_9259,c_9264]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21017,plain,
% 7.52/1.51      ( k1_relat_1(sK9(sK12,sK11,sK13)) = sK11 ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_9255,c_12027]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_29,plain,
% 7.52/1.51      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK9(X0,X1,X3) = X3 ),
% 7.52/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9263,plain,
% 7.52/1.51      ( sK9(X0,X1,X2) = X2
% 7.52/1.51      | sP0(X0,X1,X3) != iProver_top
% 7.52/1.51      | r2_hidden(X2,X3) != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_11303,plain,
% 7.52/1.51      ( sK9(X0,X1,X2) = X2
% 7.52/1.51      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_9259,c_9263]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_18843,plain,
% 7.52/1.51      ( sK9(sK12,sK11,sK13) = sK13 ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_9255,c_11303]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21042,plain,
% 7.52/1.51      ( k1_relat_1(sK13) = sK11 ),
% 7.52/1.51      inference(light_normalisation,[status(thm)],[c_21017,c_18843]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_18,plain,
% 7.52/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.52/1.51      | v1_partfun1(X0,X1)
% 7.52/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | v1_xboole_0(X2) ),
% 7.52/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_39,plain,
% 7.52/1.51      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.52/1.51      | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f113]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_666,plain,
% 7.52/1.51      ( v1_partfun1(X0,X1)
% 7.52/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.51      | ~ r2_hidden(k1_funct_1(X3,sK10(k1_relat_1(X3),X4,X3)),X4)
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_funct_1(X3)
% 7.52/1.51      | ~ v1_relat_1(X3)
% 7.52/1.51      | v1_xboole_0(X2)
% 7.52/1.51      | X3 != X0
% 7.52/1.51      | X4 != X2
% 7.52/1.51      | k1_relat_1(X3) != X1 ),
% 7.52/1.51      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_667,plain,
% 7.52/1.51      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.52/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.52/1.51      | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0)
% 7.52/1.51      | v1_xboole_0(X1) ),
% 7.52/1.51      inference(unflattening,[status(thm)],[c_666]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_37,plain,
% 7.52/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.52/1.51      | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f111]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_671,plain,
% 7.52/1.51      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.52/1.51      | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0)
% 7.52/1.51      | v1_xboole_0(X1) ),
% 7.52/1.51      inference(global_propositional_subsumption,
% 7.52/1.51                [status(thm)],
% 7.52/1.51                [c_667,c_37]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_0,plain,
% 7.52/1.51      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.52/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_687,plain,
% 7.52/1.51      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.52/1.51      | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0) ),
% 7.52/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_671,c_0]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_16,plain,
% 7.52/1.51      ( v1_funct_2(X0,X1,X2)
% 7.52/1.51      | ~ v1_partfun1(X0,X1)
% 7.52/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.51      | ~ v1_funct_1(X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_43,negated_conjecture,
% 7.52/1.51      ( ~ v1_funct_2(sK13,sK11,sK12)
% 7.52/1.51      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ v1_funct_1(sK13) ),
% 7.52/1.51      inference(cnf_transformation,[],[f102]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_695,plain,
% 7.52/1.51      ( ~ v1_partfun1(X0,X1)
% 7.52/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.51      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | sK12 != X2
% 7.52/1.51      | sK11 != X1
% 7.52/1.51      | sK13 != X0 ),
% 7.52/1.51      inference(resolution_lifted,[status(thm)],[c_16,c_43]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_696,plain,
% 7.52/1.51      ( ~ v1_partfun1(sK13,sK11)
% 7.52/1.51      | ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ v1_funct_1(sK13) ),
% 7.52/1.51      inference(unflattening,[status(thm)],[c_695]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_858,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ r2_hidden(k1_funct_1(X0,sK10(k1_relat_1(X0),X1,X0)),X1)
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(X0)
% 7.52/1.51      | k1_relat_1(X0) != sK11
% 7.52/1.51      | sK13 != X0 ),
% 7.52/1.51      inference(resolution_lifted,[status(thm)],[c_687,c_696]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_859,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ r2_hidden(k1_funct_1(sK13,sK10(k1_relat_1(sK13),X0,sK13)),X0)
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(sK13)
% 7.52/1.51      | k1_relat_1(sK13) != sK11 ),
% 7.52/1.51      inference(unflattening,[status(thm)],[c_858]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_8337,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(sK13)
% 7.52/1.51      | sP2_iProver_split
% 7.52/1.51      | k1_relat_1(sK13) != sK11 ),
% 7.52/1.51      inference(splitting,
% 7.52/1.51                [splitting(split),new_symbols(definition,[])],
% 7.52/1.51                [c_859]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9250,plain,
% 7.52/1.51      ( k1_relat_1(sK13) != sK11
% 7.52/1.51      | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top
% 7.52/1.51      | sP2_iProver_split = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_8337]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21306,plain,
% 7.52/1.51      ( sK11 != sK11
% 7.52/1.51      | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top
% 7.52/1.51      | sP2_iProver_split = iProver_top ),
% 7.52/1.51      inference(demodulation,[status(thm)],[c_21042,c_9250]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21332,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top
% 7.52/1.51      | sP2_iProver_split = iProver_top ),
% 7.52/1.51      inference(equality_resolution_simp,[status(thm)],[c_21306]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_45,plain,
% 7.52/1.51      ( r2_hidden(sK13,k1_funct_2(sK11,sK12)) = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_5,plain,
% 7.52/1.51      ( r1_tarski(X0,X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f104]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_149,plain,
% 7.52/1.51      ( r1_tarski(sK13,sK13) ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_3,plain,
% 7.52/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.52/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_153,plain,
% 7.52/1.51      ( ~ r1_tarski(sK13,sK13) | sK13 = sK13 ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_30,plain,
% 7.52/1.51      ( ~ sP0(X0,X1,X2)
% 7.52/1.51      | ~ r2_hidden(X3,X2)
% 7.52/1.51      | v1_funct_1(sK9(X0,X1,X3)) ),
% 7.52/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9633,plain,
% 7.52/1.51      ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
% 7.52/1.51      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.52/1.51      | v1_funct_1(sK9(X0,X1,sK13)) ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_30]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9736,plain,
% 7.52/1.51      ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
% 7.52/1.51      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.52/1.51      | v1_funct_1(sK9(sK12,sK11,sK13)) ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_9633]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9738,plain,
% 7.52/1.51      ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
% 7.52/1.51      | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top
% 7.52/1.51      | v1_funct_1(sK9(sK12,sK11,sK13)) = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_9736]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9737,plain,
% 7.52/1.51      ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_33]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9740,plain,
% 7.52/1.51      ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_9737]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_8350,plain,
% 7.52/1.51      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.52/1.51      theory(equality) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9902,plain,
% 7.52/1.51      ( v1_funct_1(X0)
% 7.52/1.51      | ~ v1_funct_1(sK9(sK12,sK11,sK13))
% 7.52/1.51      | X0 != sK9(sK12,sK11,sK13) ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_8350]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9903,plain,
% 7.52/1.51      ( X0 != sK9(sK12,sK11,sK13)
% 7.52/1.51      | v1_funct_1(X0) = iProver_top
% 7.52/1.51      | v1_funct_1(sK9(sK12,sK11,sK13)) != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_9902]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9905,plain,
% 7.52/1.51      ( sK13 != sK9(sK12,sK11,sK13)
% 7.52/1.51      | v1_funct_1(sK9(sK12,sK11,sK13)) != iProver_top
% 7.52/1.51      | v1_funct_1(sK13) = iProver_top ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_9903]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_31,plain,
% 7.52/1.51      ( ~ sP0(X0,X1,X2)
% 7.52/1.51      | ~ r2_hidden(X3,X2)
% 7.52/1.51      | v1_relat_1(sK9(X0,X1,X3)) ),
% 7.52/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9638,plain,
% 7.52/1.51      ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
% 7.52/1.51      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.52/1.51      | v1_relat_1(sK9(X0,X1,sK13)) ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_31]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9939,plain,
% 7.52/1.51      ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
% 7.52/1.51      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.52/1.51      | v1_relat_1(sK9(sK12,sK11,sK13)) ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_9638]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9941,plain,
% 7.52/1.51      ( sP0(sK12,sK11,k1_funct_2(sK11,sK12)) != iProver_top
% 7.52/1.51      | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top
% 7.52/1.51      | v1_relat_1(sK9(sK12,sK11,sK13)) = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_9939]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9682,plain,
% 7.52/1.51      ( ~ sP0(X0,X1,k1_funct_2(sK11,sK12))
% 7.52/1.51      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.52/1.51      | sK9(X0,X1,sK13) = sK13 ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_29]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9938,plain,
% 7.52/1.51      ( ~ sP0(sK12,sK11,k1_funct_2(sK11,sK12))
% 7.52/1.51      | ~ r2_hidden(sK13,k1_funct_2(sK11,sK12))
% 7.52/1.51      | sK9(sK12,sK11,sK13) = sK13 ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_9682]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_8349,plain,
% 7.52/1.51      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.52/1.51      theory(equality) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_10017,plain,
% 7.52/1.51      ( v1_relat_1(X0)
% 7.52/1.51      | ~ v1_relat_1(sK9(sK12,sK11,sK13))
% 7.52/1.51      | X0 != sK9(sK12,sK11,sK13) ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_8349]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_10023,plain,
% 7.52/1.51      ( X0 != sK9(sK12,sK11,sK13)
% 7.52/1.51      | v1_relat_1(X0) = iProver_top
% 7.52/1.51      | v1_relat_1(sK9(sK12,sK11,sK13)) != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_10017]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_10025,plain,
% 7.52/1.51      ( sK13 != sK9(sK12,sK11,sK13)
% 7.52/1.51      | v1_relat_1(sK9(sK12,sK11,sK13)) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) = iProver_top ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_10023]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_8340,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_10349,plain,
% 7.52/1.51      ( X0 != X1 | X0 = sK9(sK12,sK11,sK13) | sK9(sK12,sK11,sK13) != X1 ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_8340]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_10350,plain,
% 7.52/1.51      ( sK9(sK12,sK11,sK13) != sK13
% 7.52/1.51      | sK13 = sK9(sK12,sK11,sK13)
% 7.52/1.51      | sK13 != sK13 ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_10349]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_35,plain,
% 7.52/1.51      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_615,plain,
% 7.52/1.51      ( v1_partfun1(X0,X1)
% 7.52/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_funct_1(X3)
% 7.52/1.51      | ~ v1_relat_1(X3)
% 7.52/1.51      | v1_xboole_0(X2)
% 7.52/1.51      | X3 != X0
% 7.52/1.51      | k2_relat_1(X3) != X2
% 7.52/1.51      | k1_relat_1(X3) != X1 ),
% 7.52/1.51      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_616,plain,
% 7.52/1.51      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.52/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0)
% 7.52/1.51      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.52/1.51      inference(unflattening,[status(thm)],[c_615]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_34,plain,
% 7.52/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_620,plain,
% 7.52/1.51      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0)
% 7.52/1.51      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.52/1.51      inference(global_propositional_subsumption,
% 7.52/1.51                [status(thm)],
% 7.52/1.51                [c_616,c_34]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_903,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(X0)
% 7.52/1.51      | v1_xboole_0(k2_relat_1(X0))
% 7.52/1.51      | k1_relat_1(X0) != sK11
% 7.52/1.51      | sK13 != X0 ),
% 7.52/1.51      inference(resolution_lifted,[status(thm)],[c_620,c_696]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_904,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(sK13)
% 7.52/1.51      | v1_xboole_0(k2_relat_1(sK13))
% 7.52/1.51      | k1_relat_1(sK13) != sK11 ),
% 7.52/1.51      inference(unflattening,[status(thm)],[c_903]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_972,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ r2_hidden(X0,X1)
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(sK13)
% 7.52/1.51      | k2_relat_1(sK13) != X1
% 7.52/1.51      | k1_relat_1(sK13) != sK11 ),
% 7.52/1.51      inference(resolution_lifted,[status(thm)],[c_0,c_904]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_973,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ r2_hidden(X0,k2_relat_1(sK13))
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(sK13)
% 7.52/1.51      | k1_relat_1(sK13) != sK11 ),
% 7.52/1.51      inference(unflattening,[status(thm)],[c_972]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_8333,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(sK13)
% 7.52/1.51      | sP0_iProver_split
% 7.52/1.51      | k1_relat_1(sK13) != sK11 ),
% 7.52/1.51      inference(splitting,
% 7.52/1.51                [splitting(split),new_symbols(definition,[])],
% 7.52/1.51                [c_973]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9246,plain,
% 7.52/1.51      ( k1_relat_1(sK13) != sK11
% 7.52/1.51      | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top
% 7.52/1.51      | sP0_iProver_split = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_8333]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21303,plain,
% 7.52/1.51      ( sK11 != sK11
% 7.52/1.51      | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top
% 7.52/1.51      | sP0_iProver_split = iProver_top ),
% 7.52/1.51      inference(demodulation,[status(thm)],[c_21042,c_9246]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21351,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top
% 7.52/1.51      | sP0_iProver_split = iProver_top ),
% 7.52/1.51      inference(equality_resolution_simp,[status(thm)],[c_21303]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_38,plain,
% 7.52/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.52/1.51      | r2_hidden(sK10(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f112]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9256,plain,
% 7.52/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.52/1.51      | r2_hidden(sK10(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
% 7.52/1.51      | v1_funct_1(X0) != iProver_top
% 7.52/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21777,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK13),X0))) = iProver_top
% 7.52/1.51      | r2_hidden(sK10(sK11,X0,sK13),sK11) = iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_21042,c_9256]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21783,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0))) = iProver_top
% 7.52/1.51      | r2_hidden(sK10(sK11,X0,sK13),sK11) = iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top ),
% 7.52/1.51      inference(light_normalisation,[status(thm)],[c_21777,c_21042]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_30786,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,X0))) = iProver_top
% 7.52/1.51      | r2_hidden(sK10(sK11,X0,sK13),sK11) = iProver_top ),
% 7.52/1.51      inference(global_propositional_subsumption,
% 7.52/1.51                [status(thm)],
% 7.52/1.51                [c_21783,c_44,c_45,c_149,c_153,c_9738,c_9737,c_9740,
% 7.52/1.51                 c_9905,c_9941,c_9938,c_10025,c_10350]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_40,plain,
% 7.52/1.51      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.52/1.51      | r2_hidden(sK10(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_relat_1(X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f114]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_727,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | r2_hidden(sK10(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.52/1.51      | ~ v1_funct_1(X0)
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(X0)
% 7.52/1.51      | k1_relat_1(X0) != sK11
% 7.52/1.51      | sK12 != X1
% 7.52/1.51      | sK13 != X0 ),
% 7.52/1.51      inference(resolution_lifted,[status(thm)],[c_40,c_43]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_728,plain,
% 7.52/1.51      ( ~ m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12)))
% 7.52/1.51      | r2_hidden(sK10(k1_relat_1(sK13),sK12,sK13),k1_relat_1(sK13))
% 7.52/1.51      | ~ v1_funct_1(sK13)
% 7.52/1.51      | ~ v1_relat_1(sK13)
% 7.52/1.51      | k1_relat_1(sK13) != sK11 ),
% 7.52/1.51      inference(unflattening,[status(thm)],[c_727]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9252,plain,
% 7.52/1.51      ( k1_relat_1(sK13) != sK11
% 7.52/1.51      | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | r2_hidden(sK10(k1_relat_1(sK13),sK12,sK13),k1_relat_1(sK13)) = iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21308,plain,
% 7.52/1.51      ( sK11 != sK11
% 7.52/1.51      | m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | r2_hidden(sK10(sK11,sK12,sK13),sK11) = iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top ),
% 7.52/1.51      inference(demodulation,[status(thm)],[c_21042,c_9252]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21319,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | r2_hidden(sK10(sK11,sK12,sK13),sK11) = iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top ),
% 7.52/1.51      inference(equality_resolution_simp,[status(thm)],[c_21308]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_23536,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top
% 7.52/1.51      | r2_hidden(sK10(sK11,sK12,sK13),sK11) = iProver_top ),
% 7.52/1.51      inference(global_propositional_subsumption,
% 7.52/1.51                [status(thm)],
% 7.52/1.51                [c_21319,c_44,c_45,c_149,c_153,c_9738,c_9737,c_9740,
% 7.52/1.51                 c_9905,c_9941,c_9938,c_10025,c_10350]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_30797,plain,
% 7.52/1.51      ( r2_hidden(sK10(sK11,sK12,sK13),sK11) = iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_30786,c_23536]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_11,plain,
% 7.52/1.51      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.52/1.51      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 7.52/1.51      inference(cnf_transformation,[],[f106]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9277,plain,
% 7.52/1.51      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.52/1.51      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9258,plain,
% 7.52/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.52/1.51      | v1_funct_1(X0) != iProver_top
% 7.52/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_21775,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,k2_relat_1(sK13)))) = iProver_top
% 7.52/1.51      | v1_funct_1(sK13) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_21042,c_9258]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_23043,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,k2_relat_1(sK13)))) = iProver_top ),
% 7.52/1.51      inference(global_propositional_subsumption,
% 7.52/1.51                [status(thm)],
% 7.52/1.51                [c_21775,c_44,c_45,c_149,c_153,c_9738,c_9737,c_9740,
% 7.52/1.51                 c_9905,c_9941,c_9938,c_10025,c_10350]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_13,plain,
% 7.52/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.52/1.51      | ~ r2_hidden(X3,X0)
% 7.52/1.51      | r2_hidden(sK6(X3,X1,X2),X2) ),
% 7.52/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9275,plain,
% 7.52/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.52/1.51      | r2_hidden(X3,X0) != iProver_top
% 7.52/1.51      | r2_hidden(sK6(X3,X1,X2),X2) = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_23049,plain,
% 7.52/1.51      ( r2_hidden(X0,sK13) != iProver_top
% 7.52/1.51      | r2_hidden(sK6(X0,sK11,k2_relat_1(sK13)),k2_relat_1(sK13)) = iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_23043,c_9275]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_8332,plain,
% 7.52/1.51      ( ~ r2_hidden(X0,k2_relat_1(sK13)) | ~ sP0_iProver_split ),
% 7.52/1.51      inference(splitting,
% 7.52/1.51                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.52/1.51                [c_973]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9247,plain,
% 7.52/1.51      ( r2_hidden(X0,k2_relat_1(sK13)) != iProver_top
% 7.52/1.51      | sP0_iProver_split != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_8332]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_27551,plain,
% 7.52/1.51      ( r2_hidden(X0,sK13) != iProver_top
% 7.52/1.51      | sP0_iProver_split != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_23049,c_9247]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_35908,plain,
% 7.52/1.51      ( r2_hidden(X0,k1_relat_1(sK13)) != iProver_top
% 7.52/1.51      | sP0_iProver_split != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_9277,c_27551]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_35979,plain,
% 7.52/1.51      ( r2_hidden(X0,sK11) != iProver_top
% 7.52/1.51      | sP0_iProver_split != iProver_top ),
% 7.52/1.51      inference(light_normalisation,[status(thm)],[c_35908,c_21042]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_36288,plain,
% 7.52/1.51      ( sP0_iProver_split != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_30797,c_35979]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_37719,plain,
% 7.52/1.51      ( m1_subset_1(sK13,k1_zfmisc_1(k2_zfmisc_1(sK11,sK12))) != iProver_top ),
% 7.52/1.51      inference(global_propositional_subsumption,
% 7.52/1.51                [status(thm)],
% 7.52/1.51                [c_21332,c_44,c_45,c_149,c_153,c_9738,c_9737,c_9740,
% 7.52/1.51                 c_9905,c_9941,c_9938,c_10025,c_10350,c_21351,c_36288]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_37725,plain,
% 7.52/1.51      ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
% 7.52/1.51      | r1_tarski(k1_relat_1(sK13),sK11) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_9276,c_37719]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_37730,plain,
% 7.52/1.51      ( r1_tarski(k2_relat_1(sK13),sK12) != iProver_top
% 7.52/1.51      | r1_tarski(sK11,sK11) != iProver_top
% 7.52/1.51      | v1_relat_1(sK13) != iProver_top ),
% 7.52/1.51      inference(light_normalisation,[status(thm)],[c_37725,c_21042]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_4,plain,
% 7.52/1.51      ( r1_tarski(X0,X0) ),
% 7.52/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_28585,plain,
% 7.52/1.51      ( r1_tarski(sK11,sK11) ),
% 7.52/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_28588,plain,
% 7.52/1.51      ( r1_tarski(sK11,sK11) = iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_28585]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_27,plain,
% 7.52/1.51      ( ~ sP0(X0,X1,X2)
% 7.52/1.51      | r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X0)
% 7.52/1.51      | ~ r2_hidden(X3,X2) ),
% 7.52/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_9265,plain,
% 7.52/1.51      ( sP0(X0,X1,X2) != iProver_top
% 7.52/1.51      | r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X0) = iProver_top
% 7.52/1.51      | r2_hidden(X3,X2) != iProver_top ),
% 7.52/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_12674,plain,
% 7.52/1.51      ( r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X0) = iProver_top
% 7.52/1.51      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_9259,c_9265]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(c_27650,plain,
% 7.52/1.51      ( r1_tarski(k2_relat_1(sK13),sK12) = iProver_top
% 7.52/1.51      | r2_hidden(sK13,k1_funct_2(sK11,sK12)) != iProver_top ),
% 7.52/1.51      inference(superposition,[status(thm)],[c_18843,c_12674]) ).
% 7.52/1.51  
% 7.52/1.51  cnf(contradiction,plain,
% 7.52/1.51      ( $false ),
% 7.52/1.51      inference(minisat,
% 7.52/1.51                [status(thm)],
% 7.52/1.51                [c_37730,c_28588,c_27650,c_10350,c_10025,c_9938,c_9941,
% 7.52/1.51                 c_9740,c_9737,c_153,c_149,c_45,c_44]) ).
% 7.52/1.51  
% 7.52/1.51  
% 7.52/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.52/1.51  
% 7.52/1.51  ------                               Statistics
% 7.52/1.51  
% 7.52/1.51  ------ General
% 7.52/1.51  
% 7.52/1.51  abstr_ref_over_cycles:                  0
% 7.52/1.51  abstr_ref_under_cycles:                 0
% 7.52/1.51  gc_basic_clause_elim:                   0
% 7.52/1.51  forced_gc_time:                         0
% 7.52/1.51  parsing_time:                           0.008
% 7.52/1.51  unif_index_cands_time:                  0.
% 7.52/1.51  unif_index_add_time:                    0.
% 7.52/1.51  orderings_time:                         0.
% 7.52/1.51  out_proof_time:                         0.013
% 7.52/1.51  total_time:                             0.837
% 7.52/1.51  num_of_symbols:                         64
% 7.52/1.51  num_of_terms:                           32733
% 7.52/1.51  
% 7.52/1.51  ------ Preprocessing
% 7.52/1.51  
% 7.52/1.51  num_of_splits:                          3
% 7.52/1.51  num_of_split_atoms:                     3
% 7.52/1.51  num_of_reused_defs:                     0
% 7.52/1.51  num_eq_ax_congr_red:                    74
% 7.52/1.51  num_of_sem_filtered_clauses:            1
% 7.52/1.51  num_of_subtypes:                        0
% 7.52/1.51  monotx_restored_types:                  0
% 7.52/1.51  sat_num_of_epr_types:                   0
% 7.52/1.51  sat_num_of_non_cyclic_types:            0
% 7.52/1.51  sat_guarded_non_collapsed_types:        0
% 7.52/1.51  num_pure_diseq_elim:                    0
% 7.52/1.51  simp_replaced_by:                       0
% 7.52/1.51  res_preprocessed:                       191
% 7.52/1.51  prep_upred:                             0
% 7.52/1.51  prep_unflattend:                        261
% 7.52/1.51  smt_new_axioms:                         0
% 7.52/1.51  pred_elim_cands:                        6
% 7.52/1.51  pred_elim:                              3
% 7.52/1.51  pred_elim_cl:                           2
% 7.52/1.51  pred_elim_cycles:                       14
% 7.52/1.51  merged_defs:                            8
% 7.52/1.51  merged_defs_ncl:                        0
% 7.52/1.51  bin_hyper_res:                          8
% 7.52/1.51  prep_cycles:                            4
% 7.52/1.51  pred_elim_time:                         0.117
% 7.52/1.51  splitting_time:                         0.
% 7.52/1.51  sem_filter_time:                        0.
% 7.52/1.51  monotx_time:                            0.
% 7.52/1.51  subtype_inf_time:                       0.
% 7.52/1.51  
% 7.52/1.51  ------ Problem properties
% 7.52/1.51  
% 7.52/1.51  clauses:                                40
% 7.52/1.51  conjectures:                            1
% 7.52/1.51  epr:                                    3
% 7.52/1.51  horn:                                   32
% 7.52/1.51  ground:                                 6
% 7.52/1.51  unary:                                  4
% 7.52/1.51  binary:                                 8
% 7.52/1.51  lits:                                   122
% 7.52/1.51  lits_eq:                                17
% 7.52/1.51  fd_pure:                                0
% 7.52/1.51  fd_pseudo:                              0
% 7.52/1.51  fd_cond:                                1
% 7.52/1.51  fd_pseudo_cond:                         4
% 7.52/1.51  ac_symbols:                             0
% 7.52/1.51  
% 7.52/1.51  ------ Propositional Solver
% 7.52/1.51  
% 7.52/1.51  prop_solver_calls:                      30
% 7.52/1.51  prop_fast_solver_calls:                 3650
% 7.52/1.51  smt_solver_calls:                       0
% 7.52/1.51  smt_fast_solver_calls:                  0
% 7.52/1.51  prop_num_of_clauses:                    12073
% 7.52/1.51  prop_preprocess_simplified:             24301
% 7.52/1.51  prop_fo_subsumed:                       74
% 7.52/1.51  prop_solver_time:                       0.
% 7.52/1.51  smt_solver_time:                        0.
% 7.52/1.51  smt_fast_solver_time:                   0.
% 7.52/1.51  prop_fast_solver_time:                  0.
% 7.52/1.51  prop_unsat_core_time:                   0.001
% 7.52/1.51  
% 7.52/1.51  ------ QBF
% 7.52/1.51  
% 7.52/1.51  qbf_q_res:                              0
% 7.52/1.51  qbf_num_tautologies:                    0
% 7.52/1.51  qbf_prep_cycles:                        0
% 7.52/1.51  
% 7.52/1.51  ------ BMC1
% 7.52/1.51  
% 7.52/1.51  bmc1_current_bound:                     -1
% 7.52/1.51  bmc1_last_solved_bound:                 -1
% 7.52/1.51  bmc1_unsat_core_size:                   -1
% 7.52/1.51  bmc1_unsat_core_parents_size:           -1
% 7.52/1.51  bmc1_merge_next_fun:                    0
% 7.52/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.52/1.51  
% 7.52/1.51  ------ Instantiation
% 7.52/1.51  
% 7.52/1.51  inst_num_of_clauses:                    2796
% 7.52/1.51  inst_num_in_passive:                    954
% 7.52/1.51  inst_num_in_active:                     969
% 7.52/1.51  inst_num_in_unprocessed:                881
% 7.52/1.51  inst_num_of_loops:                      1180
% 7.52/1.51  inst_num_of_learning_restarts:          0
% 7.52/1.51  inst_num_moves_active_passive:          208
% 7.52/1.51  inst_lit_activity:                      0
% 7.52/1.51  inst_lit_activity_moves:                0
% 7.52/1.51  inst_num_tautologies:                   0
% 7.52/1.51  inst_num_prop_implied:                  0
% 7.52/1.51  inst_num_existing_simplified:           0
% 7.52/1.51  inst_num_eq_res_simplified:             0
% 7.52/1.51  inst_num_child_elim:                    0
% 7.52/1.51  inst_num_of_dismatching_blockings:      1747
% 7.52/1.51  inst_num_of_non_proper_insts:           2777
% 7.52/1.51  inst_num_of_duplicates:                 0
% 7.52/1.51  inst_inst_num_from_inst_to_res:         0
% 7.52/1.51  inst_dismatching_checking_time:         0.
% 7.52/1.51  
% 7.52/1.51  ------ Resolution
% 7.52/1.51  
% 7.52/1.51  res_num_of_clauses:                     0
% 7.52/1.51  res_num_in_passive:                     0
% 7.52/1.51  res_num_in_active:                      0
% 7.52/1.51  res_num_of_loops:                       195
% 7.52/1.51  res_forward_subset_subsumed:            108
% 7.52/1.51  res_backward_subset_subsumed:           18
% 7.52/1.51  res_forward_subsumed:                   0
% 7.52/1.51  res_backward_subsumed:                  1
% 7.52/1.51  res_forward_subsumption_resolution:     3
% 7.52/1.51  res_backward_subsumption_resolution:    0
% 7.52/1.51  res_clause_to_clause_subsumption:       2630
% 7.52/1.51  res_orphan_elimination:                 0
% 7.52/1.51  res_tautology_del:                      138
% 7.52/1.51  res_num_eq_res_simplified:              0
% 7.52/1.51  res_num_sel_changes:                    0
% 7.52/1.51  res_moves_from_active_to_pass:          0
% 7.52/1.51  
% 7.52/1.51  ------ Superposition
% 7.52/1.51  
% 7.52/1.51  sup_time_total:                         0.
% 7.52/1.51  sup_time_generating:                    0.
% 7.52/1.51  sup_time_sim_full:                      0.
% 7.52/1.51  sup_time_sim_immed:                     0.
% 7.52/1.51  
% 7.52/1.51  sup_num_of_clauses:                     720
% 7.52/1.51  sup_num_in_active:                      184
% 7.52/1.51  sup_num_in_passive:                     536
% 7.52/1.51  sup_num_of_loops:                       234
% 7.52/1.51  sup_fw_superposition:                   678
% 7.52/1.51  sup_bw_superposition:                   561
% 7.52/1.51  sup_immediate_simplified:               459
% 7.52/1.51  sup_given_eliminated:                   3
% 7.52/1.51  comparisons_done:                       0
% 7.52/1.51  comparisons_avoided:                    40
% 7.52/1.51  
% 7.52/1.51  ------ Simplifications
% 7.52/1.51  
% 7.52/1.51  
% 7.52/1.51  sim_fw_subset_subsumed:                 180
% 7.52/1.51  sim_bw_subset_subsumed:                 6
% 7.52/1.51  sim_fw_subsumed:                        209
% 7.52/1.51  sim_bw_subsumed:                        15
% 7.52/1.51  sim_fw_subsumption_res:                 7
% 7.52/1.51  sim_bw_subsumption_res:                 5
% 7.52/1.51  sim_tautology_del:                      3
% 7.52/1.51  sim_eq_tautology_del:                   17
% 7.52/1.51  sim_eq_res_simp:                        9
% 7.52/1.51  sim_fw_demodulated:                     5
% 7.52/1.51  sim_bw_demodulated:                     59
% 7.52/1.51  sim_light_normalised:                   66
% 7.52/1.51  sim_joinable_taut:                      0
% 7.52/1.51  sim_joinable_simp:                      0
% 7.52/1.51  sim_ac_normalised:                      0
% 7.52/1.51  sim_smt_subsumption:                    0
% 7.52/1.51  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:08:14 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 880 expanded)
%              Number of clauses        :  134 ( 303 expanded)
%              Number of leaves         :   28 ( 220 expanded)
%              Depth                    :   21
%              Number of atoms          :  834 (5243 expanded)
%              Number of equality atoms :  205 (1390 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
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

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f54,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
        & k1_relat_1(sK5(X0,X1,X6)) = X1
        & sK5(X0,X1,X6) = X6
        & v1_funct_1(sK5(X0,X1,X6))
        & v1_relat_1(sK5(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0)
        & k1_relat_1(sK4(X0,X1,X2)) = X1
        & sK4(X0,X1,X2) = X3
        & v1_funct_1(sK4(X0,X1,X2))
        & v1_relat_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
              | sK3(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK3(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK3(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0)
              & k1_relat_1(sK4(X0,X1,X2)) = X1
              & sK3(X0,X1,X2) = sK4(X0,X1,X2)
              & v1_funct_1(sK4(X0,X1,X2))
              & v1_relat_1(sK4(X0,X1,X2)) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
                & k1_relat_1(sK5(X0,X1,X6)) = X1
                & sK5(X0,X1,X6) = X6
                & v1_funct_1(sK5(X0,X1,X6))
                & v1_relat_1(sK5(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f54,f53,f52])).

fof(f84,plain,(
    ! [X6,X2,X0,X1] :
      ( sK5(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
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

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f13,f36])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f112,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f94])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
        | ~ v1_funct_2(sK9,sK7,sK8)
        | ~ v1_funct_1(sK9) )
      & r2_hidden(sK9,k1_funct_2(sK7,sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      | ~ v1_funct_2(sK9,sK7,sK8)
      | ~ v1_funct_1(sK9) )
    & r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f35,f59])).

fof(f105,plain,(
    r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f57])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f116,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f101])).

fof(f106,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f60])).

fof(f85,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK5(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f97,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f103])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_11])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_557,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_13])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_557])).

cnf(c_14712,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0)))
    | r1_tarski(k1_relat_1(sK9),sK7) ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_44411,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9))))
    | r1_tarski(k1_relat_1(sK9),sK7) ),
    inference(instantiation,[status(thm)],[c_14712])).

cnf(c_7383,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7382,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_11665,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_7383,c_7382])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK5(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_13455,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | sK5(X2,X1,X0) = X0 ),
    inference(resolution,[status(thm)],[c_30,c_34])).

cnf(c_18935,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | X0 = sK5(X2,X1,X0) ),
    inference(resolution,[status(thm)],[c_11665,c_13455])).

cnf(c_7393,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_19942,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | v1_funct_1(X0)
    | ~ v1_funct_1(sK5(X2,X1,X0)) ),
    inference(resolution,[status(thm)],[c_18935,c_7393])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK5(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2754,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_funct_1(sK5(X2,X3,X0))
    | X4 != X3
    | X5 != X2
    | k1_funct_2(X4,X5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_34])).

cnf(c_2755,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | v1_funct_1(sK5(X2,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_2754])).

cnf(c_24179,plain,
    ( v1_funct_1(X0)
    | ~ r2_hidden(X0,k1_funct_2(X1,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19942,c_2755])).

cnf(c_24180,plain,
    ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
    | v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_24179])).

cnf(c_45,negated_conjecture,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_24211,plain,
    ( v1_funct_1(sK9) ),
    inference(resolution,[status(thm)],[c_24180,c_45])).

cnf(c_41,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_44,negated_conjecture,
    ( ~ v1_funct_2(sK9,sK7,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_714,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK7
    | sK8 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_44])).

cnf(c_715,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_727,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | k1_relat_1(sK9) != sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_715,c_13])).

cnf(c_24237,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
    | k1_relat_1(sK9) != sK7 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_24211,c_727])).

cnf(c_8332,plain,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_8336,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK5(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_8341,plain,
    ( k1_relat_1(sK5(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11526,plain,
    ( k1_relat_1(sK5(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8336,c_8341])).

cnf(c_16468,plain,
    ( k1_relat_1(sK5(sK8,sK7,sK9)) = sK7 ),
    inference(superposition,[status(thm)],[c_8332,c_11526])).

cnf(c_8340,plain,
    ( sK5(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10700,plain,
    ( sK5(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8336,c_8340])).

cnf(c_13534,plain,
    ( sK5(sK8,sK7,sK9) = sK9 ),
    inference(superposition,[status(thm)],[c_8332,c_10700])).

cnf(c_16470,plain,
    ( k1_relat_1(sK9) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_16468,c_13534])).

cnf(c_24974,plain,
    ( r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24237,c_16470])).

cnf(c_24975,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9)) ),
    inference(renaming,[status(thm)],[c_24974])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25505,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ r1_tarski(k1_relat_1(sK9),X0)
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),X0) ),
    inference(resolution,[status(thm)],[c_24975,c_4])).

cnf(c_26677,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(sK9),X0)
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),X1) ),
    inference(resolution,[status(thm)],[c_25505,c_4])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_145,plain,
    ( r1_tarski(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_149,plain,
    ( ~ r1_tarski(sK9,sK9)
    | sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_602,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_603,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_35,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_607,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_35])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_682,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | sK8 != X2
    | sK7 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_44])).

cnf(c_683,plain,
    ( ~ v1_partfun1(sK9,sK7)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_836,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK7
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_607,c_683])).

cnf(c_837,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | v1_xboole_0(k2_relat_1(sK9))
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_836])).

cnf(c_626,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK6(k1_relat_1(X3),X4,X3),k1_relat_1(X3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | X4 != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_41])).

cnf(c_627,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_39,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_631,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_39])).

cnf(c_810,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X1)
    | k1_relat_1(X0) != sK7
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_631,c_683])).

cnf(c_811,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),X0,sK9),k1_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | v1_xboole_0(X0)
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_827,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),X0,sK9),k1_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(X0)
    | k1_relat_1(sK9) != sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_811,c_13])).

cnf(c_7378,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9)
    | sP0_iProver_split
    | k1_relat_1(sK9) != sK7 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_827])).

cnf(c_8780,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_funct_1(sK5(X0,X1,sK9)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_8972,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_funct_1(sK5(sK8,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_8780])).

cnf(c_8973,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_9232,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK5(sK8,sK7,sK9))
    | X0 != sK5(sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_7393])).

cnf(c_9234,plain,
    ( ~ v1_funct_1(sK5(sK8,sK7,sK9))
    | v1_funct_1(sK9)
    | sK9 != sK5(sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_9232])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK5(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_8785,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_relat_1(sK5(X0,X1,sK9)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_9240,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_relat_1(sK5(sK8,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_8785])).

cnf(c_8836,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | sK5(X0,X1,sK9) = sK9 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_9239,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | sK5(sK8,sK7,sK9) = sK9 ),
    inference(instantiation,[status(thm)],[c_8836])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8359,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8361,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9725,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8359,c_8361])).

cnf(c_9726,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9725])).

cnf(c_10251,plain,
    ( X0 != X1
    | X0 = sK5(sK8,sK7,sK9)
    | sK5(sK8,sK7,sK9) != X1 ),
    inference(instantiation,[status(thm)],[c_7383])).

cnf(c_10252,plain,
    ( sK5(sK8,sK7,sK9) != sK9
    | sK9 = sK5(sK8,sK7,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_10251])).

cnf(c_7377,plain,
    ( r2_hidden(sK6(k1_relat_1(sK9),X0,sK9),k1_relat_1(sK9))
    | v1_xboole_0(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_827])).

cnf(c_8326,plain,
    ( r2_hidden(sK6(k1_relat_1(sK9),X0,sK9),k1_relat_1(sK9)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7377])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_8355,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8331,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_9561,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8355,c_8331])).

cnf(c_10211,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9725,c_9561])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8353,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10972,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10211,c_8353])).

cnf(c_11188,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK9) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_8326,c_10972])).

cnf(c_11213,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK9)
    | ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11188])).

cnf(c_7390,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_15106,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK5(sK8,sK7,sK9))
    | X0 != sK5(sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_7390])).

cnf(c_15108,plain,
    ( ~ v1_relat_1(sK5(sK8,sK7,sK9))
    | v1_relat_1(sK9)
    | sK9 != sK5(sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_15106])).

cnf(c_8335,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8354,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10804,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8335,c_8354])).

cnf(c_19879,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(sK7,k2_relat_1(sK9))) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_16470,c_10804])).

cnf(c_46,plain,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_8974,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
    | v1_funct_1(sK5(sK8,sK7,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8972])).

cnf(c_8976,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8973])).

cnf(c_9233,plain,
    ( X0 != sK5(sK8,sK7,sK9)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK5(sK8,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9232])).

cnf(c_9235,plain,
    ( sK9 != sK5(sK8,sK7,sK9)
    | v1_funct_1(sK5(sK8,sK7,sK9)) != iProver_top
    | v1_funct_1(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9233])).

cnf(c_9242,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
    | v1_relat_1(sK5(sK8,sK7,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9240])).

cnf(c_15107,plain,
    ( X0 != sK5(sK8,sK7,sK9)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15106])).

cnf(c_15109,plain,
    ( sK9 != sK5(sK8,sK7,sK9)
    | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_15107])).

cnf(c_24141,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(sK7,k2_relat_1(sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19879,c_45,c_46,c_145,c_149,c_8974,c_8973,c_8976,c_9235,c_9242,c_9239,c_10252,c_15109])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_8351,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10694,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8355,c_8351])).

cnf(c_24150,plain,
    ( v1_xboole_0(k2_relat_1(sK9)) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_24141,c_10694])).

cnf(c_24177,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK9))
    | v1_xboole_0(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_24150])).

cnf(c_27926,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ r1_tarski(k1_relat_1(sK9),X0)
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26677,c_45,c_145,c_149,c_837,c_7378,c_8972,c_8973,c_9234,c_9240,c_9239,c_9726,c_10252,c_11213,c_15108,c_16470,c_24177])).

cnf(c_27946,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),X0) ),
    inference(resolution,[status(thm)],[c_27926,c_7])).

cnf(c_8934,plain,
    ( ~ r2_hidden(X0,X0) ),
    inference(resolution,[status(thm)],[c_12,c_7])).

cnf(c_29806,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(resolution,[status(thm)],[c_27946,c_8934])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30958,plain,
    ( ~ r1_tarski(k2_relat_1(sK9),sK8)
    | ~ r1_tarski(k1_relat_1(sK9),sK7)
    | ~ v1_relat_1(sK9) ),
    inference(resolution,[status(thm)],[c_29806,c_16])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_8342,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12563,plain,
    ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8336,c_8342])).

cnf(c_21742,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13534,c_12563])).

cnf(c_21807,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8)
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_21742])).

cnf(c_17649,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_16470,c_8335])).

cnf(c_17799,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9))))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17649])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44411,c_30958,c_21807,c_17799,c_15108,c_10252,c_9239,c_9240,c_9234,c_8973,c_8972,c_149,c_145,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:08:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.41/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.41/1.99  
% 11.41/1.99  ------  iProver source info
% 11.41/1.99  
% 11.41/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.41/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.41/1.99  git: non_committed_changes: false
% 11.41/1.99  git: last_make_outside_of_git: false
% 11.41/1.99  
% 11.41/1.99  ------ 
% 11.41/1.99  ------ Parsing...
% 11.41/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.41/1.99  ------ Proving...
% 11.41/1.99  ------ Problem Properties 
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  clauses                                 39
% 11.41/1.99  conjectures                             1
% 11.41/1.99  EPR                                     5
% 11.41/1.99  Horn                                    30
% 11.41/1.99  unary                                   3
% 11.41/1.99  binary                                  11
% 11.41/1.99  lits                                    113
% 11.41/1.99  lits eq                                 13
% 11.41/1.99  fd_pure                                 0
% 11.41/1.99  fd_pseudo                               0
% 11.41/1.99  fd_cond                                 0
% 11.41/1.99  fd_pseudo_cond                          2
% 11.41/1.99  AC symbols                              0
% 11.41/1.99  
% 11.41/1.99  ------ Input Options Time Limit: Unbounded
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  ------ 
% 11.41/1.99  Current options:
% 11.41/1.99  ------ 
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  ------ Proving...
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  % SZS status Theorem for theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  fof(f8,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f18,plain,(
% 11.41/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.41/1.99    inference(pure_predicate_removal,[],[f8])).
% 11.41/1.99  
% 11.41/1.99  fof(f23,plain,(
% 11.41/1.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.99    inference(ennf_transformation,[],[f18])).
% 11.41/1.99  
% 11.41/1.99  fof(f75,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.99    inference(cnf_transformation,[],[f23])).
% 11.41/1.99  
% 11.41/1.99  fof(f5,axiom,(
% 11.41/1.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f20,plain,(
% 11.41/1.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.41/1.99    inference(ennf_transformation,[],[f5])).
% 11.41/1.99  
% 11.41/1.99  fof(f49,plain,(
% 11.41/1.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.41/1.99    inference(nnf_transformation,[],[f20])).
% 11.41/1.99  
% 11.41/1.99  fof(f71,plain,(
% 11.41/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f49])).
% 11.41/1.99  
% 11.41/1.99  fof(f7,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f22,plain,(
% 11.41/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.99    inference(ennf_transformation,[],[f7])).
% 11.41/1.99  
% 11.41/1.99  fof(f74,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.99    inference(cnf_transformation,[],[f22])).
% 11.41/1.99  
% 11.41/1.99  fof(f36,plain,(
% 11.41/1.99    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 11.41/1.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.41/1.99  
% 11.41/1.99  fof(f50,plain,(
% 11.41/1.99    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 11.41/1.99    inference(nnf_transformation,[],[f36])).
% 11.41/1.99  
% 11.41/1.99  fof(f51,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 11.41/1.99    inference(rectify,[],[f50])).
% 11.41/1.99  
% 11.41/1.99  fof(f54,plain,(
% 11.41/1.99    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) & k1_relat_1(sK5(X0,X1,X6)) = X1 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f53,plain,(
% 11.41/1.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) & k1_relat_1(sK4(X0,X1,X2)) = X1 & sK4(X0,X1,X2) = X3 & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))))) )),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f52,plain,(
% 11.41/1.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK3(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f55,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) & k1_relat_1(sK4(X0,X1,X2)) = X1 & sK3(X0,X1,X2) = sK4(X0,X1,X2) & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) & k1_relat_1(sK5(X0,X1,X6)) = X1 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f54,f53,f52])).
% 11.41/1.99  
% 11.41/1.99  fof(f84,plain,(
% 11.41/1.99    ( ! [X6,X2,X0,X1] : (sK5(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f55])).
% 11.41/1.99  
% 11.41/1.99  fof(f13,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f37,plain,(
% 11.41/1.99    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 11.41/1.99    inference(definition_folding,[],[f13,f36])).
% 11.41/1.99  
% 11.41/1.99  fof(f56,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 11.41/1.99    inference(nnf_transformation,[],[f37])).
% 11.41/1.99  
% 11.41/1.99  fof(f94,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 11.41/1.99    inference(cnf_transformation,[],[f56])).
% 11.41/1.99  
% 11.41/1.99  fof(f112,plain,(
% 11.41/1.99    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 11.41/1.99    inference(equality_resolution,[],[f94])).
% 11.41/1.99  
% 11.41/1.99  fof(f83,plain,(
% 11.41/1.99    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f55])).
% 11.41/1.99  
% 11.41/1.99  fof(f16,conjecture,(
% 11.41/1.99    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f17,negated_conjecture,(
% 11.41/1.99    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.41/1.99    inference(negated_conjecture,[],[f16])).
% 11.41/1.99  
% 11.41/1.99  fof(f35,plain,(
% 11.41/1.99    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 11.41/1.99    inference(ennf_transformation,[],[f17])).
% 11.41/1.99  
% 11.41/1.99  fof(f59,plain,(
% 11.41/1.99    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & r2_hidden(sK9,k1_funct_2(sK7,sK8)))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f60,plain,(
% 11.41/1.99    (~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & r2_hidden(sK9,k1_funct_2(sK7,sK8))),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f35,f59])).
% 11.41/1.99  
% 11.41/1.99  fof(f105,plain,(
% 11.41/1.99    r2_hidden(sK9,k1_funct_2(sK7,sK8))),
% 11.41/1.99    inference(cnf_transformation,[],[f60])).
% 11.41/1.99  
% 11.41/1.99  fof(f15,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f33,plain,(
% 11.41/1.99    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.41/1.99    inference(ennf_transformation,[],[f15])).
% 11.41/1.99  
% 11.41/1.99  fof(f34,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.41/1.99    inference(flattening,[],[f33])).
% 11.41/1.99  
% 11.41/1.99  fof(f57,plain,(
% 11.41/1.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f58,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f57])).
% 11.41/1.99  
% 11.41/1.99  fof(f101,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK6(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f58])).
% 11.41/1.99  
% 11.41/1.99  fof(f116,plain,(
% 11.41/1.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.41/1.99    inference(equality_resolution,[],[f101])).
% 11.41/1.99  
% 11.41/1.99  fof(f106,plain,(
% 11.41/1.99    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)),
% 11.41/1.99    inference(cnf_transformation,[],[f60])).
% 11.41/1.99  
% 11.41/1.99  fof(f85,plain,(
% 11.41/1.99    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK5(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f55])).
% 11.41/1.99  
% 11.41/1.99  fof(f2,axiom,(
% 11.41/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f19,plain,(
% 11.41/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.41/1.99    inference(ennf_transformation,[],[f2])).
% 11.41/1.99  
% 11.41/1.99  fof(f42,plain,(
% 11.41/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.41/1.99    inference(nnf_transformation,[],[f19])).
% 11.41/1.99  
% 11.41/1.99  fof(f43,plain,(
% 11.41/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.41/1.99    inference(rectify,[],[f42])).
% 11.41/1.99  
% 11.41/1.99  fof(f44,plain,(
% 11.41/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f45,plain,(
% 11.41/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 11.41/1.99  
% 11.41/1.99  fof(f63,plain,(
% 11.41/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f45])).
% 11.41/1.99  
% 11.41/1.99  fof(f3,axiom,(
% 11.41/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f46,plain,(
% 11.41/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.41/1.99    inference(nnf_transformation,[],[f3])).
% 11.41/1.99  
% 11.41/1.99  fof(f47,plain,(
% 11.41/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.41/1.99    inference(flattening,[],[f46])).
% 11.41/1.99  
% 11.41/1.99  fof(f66,plain,(
% 11.41/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.41/1.99    inference(cnf_transformation,[],[f47])).
% 11.41/1.99  
% 11.41/1.99  fof(f108,plain,(
% 11.41/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.41/1.99    inference(equality_resolution,[],[f66])).
% 11.41/1.99  
% 11.41/1.99  fof(f68,plain,(
% 11.41/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f47])).
% 11.41/1.99  
% 11.41/1.99  fof(f12,axiom,(
% 11.41/1.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f29,plain,(
% 11.41/1.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.41/1.99    inference(ennf_transformation,[],[f12])).
% 11.41/1.99  
% 11.41/1.99  fof(f30,plain,(
% 11.41/1.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.41/1.99    inference(flattening,[],[f29])).
% 11.41/1.99  
% 11.41/1.99  fof(f81,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f30])).
% 11.41/1.99  
% 11.41/1.99  fof(f14,axiom,(
% 11.41/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f31,plain,(
% 11.41/1.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.41/1.99    inference(ennf_transformation,[],[f14])).
% 11.41/1.99  
% 11.41/1.99  fof(f32,plain,(
% 11.41/1.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.41/1.99    inference(flattening,[],[f31])).
% 11.41/1.99  
% 11.41/1.99  fof(f97,plain,(
% 11.41/1.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f32])).
% 11.41/1.99  
% 11.41/1.99  fof(f98,plain,(
% 11.41/1.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f32])).
% 11.41/1.99  
% 11.41/1.99  fof(f11,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f27,plain,(
% 11.41/1.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.99    inference(ennf_transformation,[],[f11])).
% 11.41/1.99  
% 11.41/1.99  fof(f28,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.99    inference(flattening,[],[f27])).
% 11.41/1.99  
% 11.41/1.99  fof(f79,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.99    inference(cnf_transformation,[],[f28])).
% 11.41/1.99  
% 11.41/1.99  fof(f103,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK6(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f58])).
% 11.41/1.99  
% 11.41/1.99  fof(f114,plain,(
% 11.41/1.99    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.41/1.99    inference(equality_resolution,[],[f103])).
% 11.41/1.99  
% 11.41/1.99  fof(f82,plain,(
% 11.41/1.99    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f55])).
% 11.41/1.99  
% 11.41/1.99  fof(f64,plain,(
% 11.41/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f45])).
% 11.41/1.99  
% 11.41/1.99  fof(f1,axiom,(
% 11.41/1.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f38,plain,(
% 11.41/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.41/1.99    inference(nnf_transformation,[],[f1])).
% 11.41/1.99  
% 11.41/1.99  fof(f39,plain,(
% 11.41/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.41/1.99    inference(rectify,[],[f38])).
% 11.41/1.99  
% 11.41/1.99  fof(f40,plain,(
% 11.41/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f41,plain,(
% 11.41/1.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 11.41/1.99  
% 11.41/1.99  fof(f61,plain,(
% 11.41/1.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f41])).
% 11.41/1.99  
% 11.41/1.99  fof(f4,axiom,(
% 11.41/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f48,plain,(
% 11.41/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.41/1.99    inference(nnf_transformation,[],[f4])).
% 11.41/1.99  
% 11.41/1.99  fof(f70,plain,(
% 11.41/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f48])).
% 11.41/1.99  
% 11.41/1.99  fof(f6,axiom,(
% 11.41/1.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f21,plain,(
% 11.41/1.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.41/1.99    inference(ennf_transformation,[],[f6])).
% 11.41/1.99  
% 11.41/1.99  fof(f73,plain,(
% 11.41/1.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f21])).
% 11.41/1.99  
% 11.41/1.99  fof(f69,plain,(
% 11.41/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.41/1.99    inference(cnf_transformation,[],[f48])).
% 11.41/1.99  
% 11.41/1.99  fof(f9,axiom,(
% 11.41/1.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f24,plain,(
% 11.41/1.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 11.41/1.99    inference(ennf_transformation,[],[f9])).
% 11.41/1.99  
% 11.41/1.99  fof(f76,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f24])).
% 11.41/1.99  
% 11.41/1.99  fof(f10,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f25,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 11.41/1.99    inference(ennf_transformation,[],[f10])).
% 11.41/1.99  
% 11.41/1.99  fof(f26,plain,(
% 11.41/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 11.41/1.99    inference(flattening,[],[f25])).
% 11.41/1.99  
% 11.41/1.99  fof(f77,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f26])).
% 11.41/1.99  
% 11.41/1.99  fof(f86,plain,(
% 11.41/1.99    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f55])).
% 11.41/1.99  
% 11.41/1.99  cnf(c_14,plain,
% 11.41/1.99      ( v4_relat_1(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.41/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_11,plain,
% 11.41/1.99      ( ~ v4_relat_1(X0,X1)
% 11.41/1.99      | r1_tarski(k1_relat_1(X0),X1)
% 11.41/1.99      | ~ v1_relat_1(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_553,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | r1_tarski(k1_relat_1(X0),X1)
% 11.41/1.99      | ~ v1_relat_1(X0) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_14,c_11]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_13,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | v1_relat_1(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_557,plain,
% 11.41/1.99      ( r1_tarski(k1_relat_1(X0),X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_553,c_13]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_558,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_557]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_14712,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0)))
% 11.41/1.99      | r1_tarski(k1_relat_1(sK9),sK7) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_558]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44411,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9))))
% 11.41/1.99      | r1_tarski(k1_relat_1(sK9),sK7) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_14712]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7383,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7382,plain,( X0 = X0 ),theory(equality) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_11665,plain,
% 11.41/1.99      ( X0 != X1 | X1 = X0 ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_7383,c_7382]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_30,plain,
% 11.41/1.99      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK5(X0,X1,X3) = X3 ),
% 11.41/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_34,plain,
% 11.41/1.99      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 11.41/1.99      inference(cnf_transformation,[],[f112]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_13455,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,k1_funct_2(X1,X2)) | sK5(X2,X1,X0) = X0 ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_30,c_34]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_18935,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,k1_funct_2(X1,X2)) | X0 = sK5(X2,X1,X0) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_11665,c_13455]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7393,plain,
% 11.41/1.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 11.41/1.99      theory(equality) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_19942,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,k1_funct_2(X1,X2))
% 11.41/1.99      | v1_funct_1(X0)
% 11.41/1.99      | ~ v1_funct_1(sK5(X2,X1,X0)) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_18935,c_7393]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_31,plain,
% 11.41/1.99      ( ~ sP0(X0,X1,X2)
% 11.41/1.99      | ~ r2_hidden(X3,X2)
% 11.41/1.99      | v1_funct_1(sK5(X0,X1,X3)) ),
% 11.41/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_2754,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,X1)
% 11.41/1.99      | v1_funct_1(sK5(X2,X3,X0))
% 11.41/1.99      | X4 != X3
% 11.41/1.99      | X5 != X2
% 11.41/1.99      | k1_funct_2(X4,X5) != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_31,c_34]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_2755,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,k1_funct_2(X1,X2)) | v1_funct_1(sK5(X2,X1,X0)) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_2754]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24179,plain,
% 11.41/1.99      ( v1_funct_1(X0) | ~ r2_hidden(X0,k1_funct_2(X1,X2)) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_19942,c_2755]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24180,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,k1_funct_2(X1,X2)) | v1_funct_1(X0) ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_24179]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_45,negated_conjecture,
% 11.41/1.99      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
% 11.41/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24211,plain,
% 11.41/1.99      ( v1_funct_1(sK9) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_24180,c_45]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_41,plain,
% 11.41/1.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_relat_1(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f116]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44,negated_conjecture,
% 11.41/1.99      ( ~ v1_funct_2(sK9,sK7,sK8)
% 11.41/1.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | ~ v1_funct_1(sK9) ),
% 11.41/1.99      inference(cnf_transformation,[],[f106]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_714,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | ~ v1_relat_1(X0)
% 11.41/1.99      | k1_relat_1(X0) != sK7
% 11.41/1.99      | sK8 != X1
% 11.41/1.99      | sK9 != X0 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_41,c_44]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_715,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | ~ v1_relat_1(sK9)
% 11.41/1.99      | k1_relat_1(sK9) != sK7 ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_714]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_727,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | k1_relat_1(sK9) != sK7 ),
% 11.41/1.99      inference(forward_subsumption_resolution,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_715,c_13]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24237,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
% 11.41/1.99      | k1_relat_1(sK9) != sK7 ),
% 11.41/1.99      inference(backward_subsumption_resolution,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_24211,c_727]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8332,plain,
% 11.41/1.99      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8336,plain,
% 11.41/1.99      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_29,plain,
% 11.41/1.99      ( ~ sP0(X0,X1,X2)
% 11.41/1.99      | ~ r2_hidden(X3,X2)
% 11.41/1.99      | k1_relat_1(sK5(X0,X1,X3)) = X1 ),
% 11.41/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8341,plain,
% 11.41/1.99      ( k1_relat_1(sK5(X0,X1,X2)) = X1
% 11.41/1.99      | sP0(X0,X1,X3) != iProver_top
% 11.41/1.99      | r2_hidden(X2,X3) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_11526,plain,
% 11.41/1.99      ( k1_relat_1(sK5(X0,X1,X2)) = X1
% 11.41/1.99      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8336,c_8341]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_16468,plain,
% 11.41/1.99      ( k1_relat_1(sK5(sK8,sK7,sK9)) = sK7 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8332,c_11526]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8340,plain,
% 11.41/1.99      ( sK5(X0,X1,X2) = X2
% 11.41/1.99      | sP0(X0,X1,X3) != iProver_top
% 11.41/1.99      | r2_hidden(X2,X3) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_10700,plain,
% 11.41/1.99      ( sK5(X0,X1,X2) = X2
% 11.41/1.99      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8336,c_8340]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_13534,plain,
% 11.41/1.99      ( sK5(sK8,sK7,sK9) = sK9 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8332,c_10700]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_16470,plain,
% 11.41/1.99      ( k1_relat_1(sK9) = sK7 ),
% 11.41/1.99      inference(light_normalisation,[status(thm)],[c_16468,c_13534]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24974,plain,
% 11.41/1.99      ( r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
% 11.41/1.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_24237,c_16470]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24975,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9)) ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_24974]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4,plain,
% 11.41/1.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_25505,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | ~ r1_tarski(k1_relat_1(sK9),X0)
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),X0) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_24975,c_4]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_26677,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | ~ r1_tarski(X0,X1)
% 11.41/1.99      | ~ r1_tarski(k1_relat_1(sK9),X0)
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),X1) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_25505,c_4]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7,plain,
% 11.41/1.99      ( r1_tarski(X0,X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f108]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_145,plain,
% 11.41/1.99      ( r1_tarski(sK9,sK9) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_5,plain,
% 11.41/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.41/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_149,plain,
% 11.41/1.99      ( ~ r1_tarski(sK9,sK9) | sK9 = sK9 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_19,plain,
% 11.41/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.41/1.99      | v1_partfun1(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | v1_xboole_0(X2) ),
% 11.41/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_36,plain,
% 11.41/1.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_relat_1(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_602,plain,
% 11.41/1.99      ( v1_partfun1(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_funct_1(X3)
% 11.41/1.99      | ~ v1_relat_1(X3)
% 11.41/1.99      | v1_xboole_0(X2)
% 11.41/1.99      | X3 != X0
% 11.41/1.99      | k2_relat_1(X3) != X2
% 11.41/1.99      | k1_relat_1(X3) != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_603,plain,
% 11.41/1.99      ( v1_partfun1(X0,k1_relat_1(X0))
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_relat_1(X0)
% 11.41/1.99      | v1_xboole_0(k2_relat_1(X0)) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_602]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_35,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_relat_1(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_607,plain,
% 11.41/1.99      ( v1_partfun1(X0,k1_relat_1(X0))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_relat_1(X0)
% 11.41/1.99      | v1_xboole_0(k2_relat_1(X0)) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_603,c_35]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_17,plain,
% 11.41/1.99      ( v1_funct_2(X0,X1,X2)
% 11.41/1.99      | ~ v1_partfun1(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | ~ v1_funct_1(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_682,plain,
% 11.41/1.99      ( ~ v1_partfun1(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | sK8 != X2
% 11.41/1.99      | sK7 != X1
% 11.41/1.99      | sK9 != X0 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_44]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_683,plain,
% 11.41/1.99      ( ~ v1_partfun1(sK9,sK7)
% 11.41/1.99      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | ~ v1_funct_1(sK9) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_682]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_836,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | ~ v1_relat_1(X0)
% 11.41/1.99      | v1_xboole_0(k2_relat_1(X0))
% 11.41/1.99      | k1_relat_1(X0) != sK7
% 11.41/1.99      | sK9 != X0 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_607,c_683]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_837,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | ~ v1_relat_1(sK9)
% 11.41/1.99      | v1_xboole_0(k2_relat_1(sK9))
% 11.41/1.99      | k1_relat_1(sK9) != sK7 ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_836]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_626,plain,
% 11.41/1.99      ( v1_partfun1(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(X3),X4,X3),k1_relat_1(X3))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_funct_1(X3)
% 11.41/1.99      | ~ v1_relat_1(X3)
% 11.41/1.99      | v1_xboole_0(X2)
% 11.41/1.99      | X3 != X0
% 11.41/1.99      | X4 != X2
% 11.41/1.99      | k1_relat_1(X3) != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_41]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_627,plain,
% 11.41/1.99      ( v1_partfun1(X0,k1_relat_1(X0))
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_relat_1(X0)
% 11.41/1.99      | v1_xboole_0(X1) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_626]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_39,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_relat_1(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f114]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_631,plain,
% 11.41/1.99      ( v1_partfun1(X0,k1_relat_1(X0))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_relat_1(X0)
% 11.41/1.99      | v1_xboole_0(X1) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_627,c_39]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_810,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 11.41/1.99      | ~ v1_funct_1(X0)
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | ~ v1_relat_1(X0)
% 11.41/1.99      | v1_xboole_0(X1)
% 11.41/1.99      | k1_relat_1(X0) != sK7
% 11.41/1.99      | sK9 != X0 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_631,c_683]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_811,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),X0,sK9),k1_relat_1(sK9))
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | ~ v1_relat_1(sK9)
% 11.41/1.99      | v1_xboole_0(X0)
% 11.41/1.99      | k1_relat_1(sK9) != sK7 ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_810]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_827,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),X0,sK9),k1_relat_1(sK9))
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | v1_xboole_0(X0)
% 11.41/1.99      | k1_relat_1(sK9) != sK7 ),
% 11.41/1.99      inference(forward_subsumption_resolution,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_811,c_13]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7378,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | sP0_iProver_split
% 11.41/1.99      | k1_relat_1(sK9) != sK7 ),
% 11.41/1.99      inference(splitting,
% 11.41/1.99                [splitting(split),new_symbols(definition,[])],
% 11.41/1.99                [c_827]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8780,plain,
% 11.41/1.99      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 11.41/1.99      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 11.41/1.99      | v1_funct_1(sK5(X0,X1,sK9)) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_31]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8972,plain,
% 11.41/1.99      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 11.41/1.99      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 11.41/1.99      | v1_funct_1(sK5(sK8,sK7,sK9)) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_8780]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8973,plain,
% 11.41/1.99      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_34]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9232,plain,
% 11.41/1.99      ( v1_funct_1(X0)
% 11.41/1.99      | ~ v1_funct_1(sK5(sK8,sK7,sK9))
% 11.41/1.99      | X0 != sK5(sK8,sK7,sK9) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_7393]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9234,plain,
% 11.41/1.99      ( ~ v1_funct_1(sK5(sK8,sK7,sK9))
% 11.41/1.99      | v1_funct_1(sK9)
% 11.41/1.99      | sK9 != sK5(sK8,sK7,sK9) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_9232]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_32,plain,
% 11.41/1.99      ( ~ sP0(X0,X1,X2)
% 11.41/1.99      | ~ r2_hidden(X3,X2)
% 11.41/1.99      | v1_relat_1(sK5(X0,X1,X3)) ),
% 11.41/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8785,plain,
% 11.41/1.99      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 11.41/1.99      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 11.41/1.99      | v1_relat_1(sK5(X0,X1,sK9)) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_32]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9240,plain,
% 11.41/1.99      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 11.41/1.99      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 11.41/1.99      | v1_relat_1(sK5(sK8,sK7,sK9)) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_8785]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8836,plain,
% 11.41/1.99      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 11.41/1.99      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 11.41/1.99      | sK5(X0,X1,sK9) = sK9 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_30]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9239,plain,
% 11.41/1.99      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 11.41/1.99      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 11.41/1.99      | sK5(sK8,sK7,sK9) = sK9 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_8836]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_3,plain,
% 11.41/1.99      ( r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8359,plain,
% 11.41/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.41/1.99      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8361,plain,
% 11.41/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.41/1.99      | v1_xboole_0(X1) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9725,plain,
% 11.41/1.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8359,c_8361]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9726,plain,
% 11.41/1.99      ( r1_tarski(X0,X1) | ~ v1_xboole_0(X0) ),
% 11.41/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_9725]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_10251,plain,
% 11.41/1.99      ( X0 != X1 | X0 = sK5(sK8,sK7,sK9) | sK5(sK8,sK7,sK9) != X1 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_7383]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_10252,plain,
% 11.41/1.99      ( sK5(sK8,sK7,sK9) != sK9 | sK9 = sK5(sK8,sK7,sK9) | sK9 != sK9 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_10251]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7377,plain,
% 11.41/1.99      ( r2_hidden(sK6(k1_relat_1(sK9),X0,sK9),k1_relat_1(sK9))
% 11.41/1.99      | v1_xboole_0(X0)
% 11.41/1.99      | ~ sP0_iProver_split ),
% 11.41/1.99      inference(splitting,
% 11.41/1.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 11.41/1.99                [c_827]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8326,plain,
% 11.41/1.99      ( r2_hidden(sK6(k1_relat_1(sK9),X0,sK9),k1_relat_1(sK9)) = iProver_top
% 11.41/1.99      | v1_xboole_0(X0) = iProver_top
% 11.41/1.99      | sP0_iProver_split != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_7377]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8355,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.41/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8331,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.41/1.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9561,plain,
% 11.41/1.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.41/1.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8355,c_8331]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_10211,plain,
% 11.41/1.99      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 11.41/1.99      | v1_xboole_0(X0) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_9725,c_9561]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_12,plain,
% 11.41/1.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8353,plain,
% 11.41/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.41/1.99      | r2_hidden(X1,X0) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_10972,plain,
% 11.41/1.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 11.41/1.99      | v1_xboole_0(X1) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_10211,c_8353]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_11188,plain,
% 11.41/1.99      ( v1_xboole_0(X0) = iProver_top
% 11.41/1.99      | v1_xboole_0(sK9) != iProver_top
% 11.41/1.99      | sP0_iProver_split != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8326,c_10972]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_11213,plain,
% 11.41/1.99      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK9) | ~ sP0_iProver_split ),
% 11.41/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_11188]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7390,plain,
% 11.41/1.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 11.41/1.99      theory(equality) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_15106,plain,
% 11.41/1.99      ( v1_relat_1(X0)
% 11.41/1.99      | ~ v1_relat_1(sK5(sK8,sK7,sK9))
% 11.41/1.99      | X0 != sK5(sK8,sK7,sK9) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_7390]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_15108,plain,
% 11.41/1.99      ( ~ v1_relat_1(sK5(sK8,sK7,sK9))
% 11.41/1.99      | v1_relat_1(sK9)
% 11.41/1.99      | sK9 != sK5(sK8,sK7,sK9) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_15106]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8335,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 11.41/1.99      | v1_funct_1(X0) != iProver_top
% 11.41/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8354,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.41/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_10804,plain,
% 11.41/1.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 11.41/1.99      | v1_funct_1(X0) != iProver_top
% 11.41/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8335,c_8354]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_19879,plain,
% 11.41/1.99      ( r1_tarski(sK9,k2_zfmisc_1(sK7,k2_relat_1(sK9))) = iProver_top
% 11.41/1.99      | v1_funct_1(sK9) != iProver_top
% 11.41/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_16470,c_10804]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_46,plain,
% 11.41/1.99      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8974,plain,
% 11.41/1.99      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
% 11.41/1.99      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
% 11.41/1.99      | v1_funct_1(sK5(sK8,sK7,sK9)) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_8972]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8976,plain,
% 11.41/1.99      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_8973]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9233,plain,
% 11.41/1.99      ( X0 != sK5(sK8,sK7,sK9)
% 11.41/1.99      | v1_funct_1(X0) = iProver_top
% 11.41/1.99      | v1_funct_1(sK5(sK8,sK7,sK9)) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_9232]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9235,plain,
% 11.41/1.99      ( sK9 != sK5(sK8,sK7,sK9)
% 11.41/1.99      | v1_funct_1(sK5(sK8,sK7,sK9)) != iProver_top
% 11.41/1.99      | v1_funct_1(sK9) = iProver_top ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_9233]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9242,plain,
% 11.41/1.99      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
% 11.41/1.99      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
% 11.41/1.99      | v1_relat_1(sK5(sK8,sK7,sK9)) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_9240]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_15107,plain,
% 11.41/1.99      ( X0 != sK5(sK8,sK7,sK9)
% 11.41/1.99      | v1_relat_1(X0) = iProver_top
% 11.41/1.99      | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_15106]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_15109,plain,
% 11.41/1.99      ( sK9 != sK5(sK8,sK7,sK9)
% 11.41/1.99      | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top
% 11.41/1.99      | v1_relat_1(sK9) = iProver_top ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_15107]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24141,plain,
% 11.41/1.99      ( r1_tarski(sK9,k2_zfmisc_1(sK7,k2_relat_1(sK9))) = iProver_top ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_19879,c_45,c_46,c_145,c_149,c_8974,c_8973,c_8976,
% 11.41/1.99                 c_9235,c_9242,c_9239,c_10252,c_15109]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_15,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | ~ v1_xboole_0(X2)
% 11.41/1.99      | v1_xboole_0(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8351,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.41/1.99      | v1_xboole_0(X2) != iProver_top
% 11.41/1.99      | v1_xboole_0(X0) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_10694,plain,
% 11.41/1.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.41/1.99      | v1_xboole_0(X2) != iProver_top
% 11.41/1.99      | v1_xboole_0(X0) = iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8355,c_8351]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24150,plain,
% 11.41/1.99      ( v1_xboole_0(k2_relat_1(sK9)) != iProver_top
% 11.41/1.99      | v1_xboole_0(sK9) = iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_24141,c_10694]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24177,plain,
% 11.41/1.99      ( ~ v1_xboole_0(k2_relat_1(sK9)) | v1_xboole_0(sK9) ),
% 11.41/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_24150]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_27926,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | ~ r1_tarski(k1_relat_1(sK9),X0)
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),X1) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_26677,c_45,c_145,c_149,c_837,c_7378,c_8972,c_8973,
% 11.41/1.99                 c_9234,c_9240,c_9239,c_9726,c_10252,c_11213,c_15108,
% 11.41/1.99                 c_16470,c_24177]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_27946,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 11.41/1.99      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),X0) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_27926,c_7]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8934,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,X0) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_12,c_7]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_29806,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_27946,c_8934]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_16,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 11.41/1.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 11.41/1.99      | ~ v1_relat_1(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_30958,plain,
% 11.41/1.99      ( ~ r1_tarski(k2_relat_1(sK9),sK8)
% 11.41/1.99      | ~ r1_tarski(k1_relat_1(sK9),sK7)
% 11.41/1.99      | ~ v1_relat_1(sK9) ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_29806,c_16]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_28,plain,
% 11.41/1.99      ( ~ sP0(X0,X1,X2)
% 11.41/1.99      | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0)
% 11.41/1.99      | ~ r2_hidden(X3,X2) ),
% 11.41/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8342,plain,
% 11.41/1.99      ( sP0(X0,X1,X2) != iProver_top
% 11.41/1.99      | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) = iProver_top
% 11.41/1.99      | r2_hidden(X3,X2) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_12563,plain,
% 11.41/1.99      ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) = iProver_top
% 11.41/1.99      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_8336,c_8342]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_21742,plain,
% 11.41/1.99      ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top
% 11.41/1.99      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_13534,c_12563]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_21807,plain,
% 11.41/1.99      ( r1_tarski(k2_relat_1(sK9),sK8)
% 11.41/1.99      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
% 11.41/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_21742]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_17649,plain,
% 11.41/1.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top
% 11.41/1.99      | v1_funct_1(sK9) != iProver_top
% 11.41/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_16470,c_8335]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_17799,plain,
% 11.41/1.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9))))
% 11.41/1.99      | ~ v1_funct_1(sK9)
% 11.41/1.99      | ~ v1_relat_1(sK9) ),
% 11.41/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_17649]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(contradiction,plain,
% 11.41/1.99      ( $false ),
% 11.41/1.99      inference(minisat,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_44411,c_30958,c_21807,c_17799,c_15108,c_10252,c_9239,
% 11.41/1.99                 c_9240,c_9234,c_8973,c_8972,c_149,c_145,c_45]) ).
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  ------                               Statistics
% 11.41/1.99  
% 11.41/1.99  ------ Selected
% 11.41/1.99  
% 11.41/1.99  total_time:                             1.103
% 11.41/1.99  
%------------------------------------------------------------------------------

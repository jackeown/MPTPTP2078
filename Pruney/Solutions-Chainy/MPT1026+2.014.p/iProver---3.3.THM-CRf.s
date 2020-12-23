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
% DateTime   : Thu Dec  3 12:08:15 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  231 (1472 expanded)
%              Number of clauses        :  141 ( 498 expanded)
%              Number of leaves         :   28 ( 375 expanded)
%              Depth                    :   20
%              Number of atoms          :  834 (8918 expanded)
%              Number of equality atoms :  346 (2874 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f56,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
        | ~ v1_funct_2(sK8,sK6,sK7)
        | ~ v1_funct_1(sK8) )
      & r2_hidden(sK8,k1_funct_2(sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      | ~ v1_funct_2(sK8,sK6,sK7)
      | ~ v1_funct_1(sK8) )
    & r2_hidden(sK8,k1_funct_2(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f56])).

fof(f105,plain,(
    r2_hidden(sK8,k1_funct_2(sK6,sK7)) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
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

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f15,f36])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f94])).

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
    inference(nnf_transformation,[],[f36])).

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
     => ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
        & k1_relat_1(sK4(X0,X1,X6)) = X1
        & sK4(X0,X1,X6) = X6
        & v1_funct_1(sK4(X0,X1,X6))
        & v1_relat_1(sK4(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0)
        & k1_relat_1(sK3(X0,X1,X2)) = X1
        & sK3(X0,X1,X2) = X3
        & v1_funct_1(sK3(X0,X1,X2))
        & v1_relat_1(sK3(X0,X1,X2)) ) ) ),
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
              | sK2(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK2(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK2(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0)
              & k1_relat_1(sK3(X0,X1,X2)) = X1
              & sK2(X0,X1,X2) = sK3(X0,X1,X2)
              & v1_funct_1(sK3(X0,X1,X2))
              & v1_relat_1(sK3(X0,X1,X2)) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
                & k1_relat_1(sK4(X0,X1,X6)) = X1
                & sK4(X0,X1,X6) = X6
                & v1_funct_1(sK4(X0,X1,X6))
                & v1_relat_1(sK4(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f51,f50,f49])).

fof(f84,plain,(
    ! [X6,X2,X0,X1] :
      ( sK4(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

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

fof(f85,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK4(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

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

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

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

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

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

fof(f106,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_2(sK8,sK6,sK7)
    | ~ v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f54])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f118,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f101])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f116,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f103])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_11033,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_23074,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK8,X2)
    | X2 != X1
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_11033])).

cnf(c_23076,plain,
    ( r1_tarski(sK8,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK8 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23074])).

cnf(c_48,negated_conjecture,
    ( r2_hidden(sK8,k1_funct_2(sK6,sK7)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_11934,plain,
    ( r2_hidden(sK8,k1_funct_2(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_37,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_11938,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_33,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK4(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_11942,plain,
    ( sK4(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_13746,plain,
    ( sK4(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11938,c_11942])).

cnf(c_13934,plain,
    ( sK4(sK7,sK6,sK8) = sK8 ),
    inference(superposition,[status(thm)],[c_11934,c_13746])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_11944,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15147,plain,
    ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11938,c_11944])).

cnf(c_22045,plain,
    ( r1_tarski(k2_relat_1(sK8),sK7) = iProver_top
    | r2_hidden(sK8,k1_funct_2(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13934,c_15147])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11952,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK4(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_11943,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_14472,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11938,c_11943])).

cnf(c_15040,plain,
    ( k1_relat_1(sK4(sK7,sK6,sK8)) = sK6 ),
    inference(superposition,[status(thm)],[c_11934,c_14472])).

cnf(c_15042,plain,
    ( k1_relat_1(sK8) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_15040,c_13934])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_39,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_570,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k1_relat_1(X3) != X1
    | k2_relat_1(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_39])).

cnf(c_571,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_38,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_575,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_38])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_47,negated_conjecture,
    ( ~ v1_funct_2(sK8,sK6,sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_642,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK8)
    | sK7 != X2
    | sK6 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_47])).

cnf(c_643,plain,
    ( ~ v1_partfun1(sK8,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK8) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_792,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK6
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_575,c_643])).

cnf(c_793,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | v1_xboole_0(k2_relat_1(sK8))
    | k1_relat_1(sK8) != sK6 ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_805,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK8)
    | v1_xboole_0(k2_relat_1(sK8))
    | k1_relat_1(sK8) != sK6 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_793,c_17])).

cnf(c_11927,plain,
    ( k1_relat_1(sK8) != sK6
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_15435,plain,
    ( sK6 != sK6
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15042,c_11927])).

cnf(c_15473,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15435])).

cnf(c_794,plain,
    ( k1_relat_1(sK8) != sK6
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_35,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11940,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_relat_1(sK4(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_14350,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_relat_1(sK4(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11938,c_11940])).

cnf(c_14739,plain,
    ( v1_relat_1(sK4(sK7,sK6,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11934,c_14350])).

cnf(c_14741,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14739,c_13934])).

cnf(c_34,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_11941,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_funct_1(sK4(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_14466,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_funct_1(sK4(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11938,c_11941])).

cnf(c_14952,plain,
    ( v1_funct_1(sK4(sK7,sK6,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11934,c_14466])).

cnf(c_14954,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14952,c_13934])).

cnf(c_17834,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15473,c_794,c_14741,c_14954,c_15042])).

cnf(c_18103,plain,
    ( r1_tarski(k1_relat_1(sK8),sK6) != iProver_top
    | r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11952,c_17834])).

cnf(c_18128,plain,
    ( r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18103,c_15042])).

cnf(c_18760,plain,
    ( r1_tarski(sK6,sK6) != iProver_top
    | r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18128,c_14741])).

cnf(c_18761,plain,
    ( r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_18760])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_11960,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_18767,plain,
    ( r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18761,c_11960])).

cnf(c_16,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_11955,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16442,plain,
    ( r1_tarski(sK6,k1_relat_1(X0)) = iProver_top
    | r1_tarski(sK8,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15042,c_11955])).

cnf(c_16635,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top
    | r1_tarski(sK6,k1_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16442,c_14741])).

cnf(c_16636,plain,
    ( r1_tarski(sK6,k1_relat_1(X0)) = iProver_top
    | r1_tarski(sK8,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16635])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_11961,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16646,plain,
    ( k1_relat_1(X0) = sK6
    | r1_tarski(k1_relat_1(X0),sK6) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16636,c_11961])).

cnf(c_17920,plain,
    ( k1_relat_1(k1_xboole_0) = sK6
    | r1_tarski(sK8,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_16646])).

cnf(c_17926,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK8,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17920,c_16])).

cnf(c_126,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_128,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_144,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_145,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_146,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_148,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_156,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12303,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_12304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12303])).

cnf(c_12306,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12304])).

cnf(c_12501,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_11033])).

cnf(c_12502,plain,
    ( X0 != X1
    | k2_zfmisc_1(X2,X3) != X4
    | r1_tarski(X1,X4) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12501])).

cnf(c_12504,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12502])).

cnf(c_11031,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_16542,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_11031])).

cnf(c_16543,plain,
    ( sK6 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16542])).

cnf(c_16545,plain,
    ( sK6 != k1_xboole_0
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16543])).

cnf(c_44,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK5(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_674,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | r2_hidden(sK5(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6
    | sK7 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_47])).

cnf(c_675,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | r2_hidden(sK5(k1_relat_1(sK8),sK7,sK8),k1_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | k1_relat_1(sK8) != sK6 ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_687,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | r2_hidden(sK5(k1_relat_1(sK8),sK7,sK8),k1_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | k1_relat_1(sK8) != sK6 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_675,c_17])).

cnf(c_11932,plain,
    ( k1_relat_1(sK8) != sK6
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r2_hidden(sK5(k1_relat_1(sK8),sK7,sK8),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_15439,plain,
    ( sK6 != sK6
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15042,c_11932])).

cnf(c_15448,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15439])).

cnf(c_17853,plain,
    ( r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15448,c_14954])).

cnf(c_17854,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_17853])).

cnf(c_42,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK5(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_11935,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r2_hidden(sK5(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_15504,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),X0))) = iProver_top
    | r2_hidden(sK5(sK6,X0,sK8),sK6) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15042,c_11935])).

cnf(c_15510,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) = iProver_top
    | r2_hidden(sK5(sK6,X0,sK8),sK6) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15504,c_15042])).

cnf(c_15832,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) = iProver_top
    | r2_hidden(sK5(sK6,X0,sK8),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15510,c_14741,c_14954])).

cnf(c_17859,plain,
    ( r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17854,c_15832])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11964,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_17861,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_17859,c_11964])).

cnf(c_18281,plain,
    ( r1_tarski(k1_xboole_0,sK6) != iProver_top
    | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17926,c_128,c_144,c_145,c_148,c_156,c_12306,c_12504,c_16545,c_17861])).

cnf(c_18282,plain,
    ( r1_tarski(sK8,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_18281])).

cnf(c_18283,plain,
    ( ~ r1_tarski(sK8,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18282])).

cnf(c_16820,plain,
    ( r1_tarski(sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_12840,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK8)
    | X2 != X0
    | sK8 != X1 ),
    inference(instantiation,[status(thm)],[c_11033])).

cnf(c_14374,plain,
    ( ~ r1_tarski(X0,sK8)
    | r1_tarski(X1,sK8)
    | X1 != X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_12840])).

cnf(c_16819,plain,
    ( r1_tarski(X0,sK8)
    | ~ r1_tarski(sK8,sK8)
    | X0 != sK8
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_14374])).

cnf(c_16822,plain,
    ( ~ r1_tarski(sK8,sK8)
    | r1_tarski(k1_xboole_0,sK8)
    | sK8 != sK8
    | k1_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_16819])).

cnf(c_16441,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_11955])).

cnf(c_16504,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16441,c_128,c_144,c_145,c_148,c_12306,c_12504])).

cnf(c_16505,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16504])).

cnf(c_16512,plain,
    ( r1_tarski(k1_xboole_0,sK6) = iProver_top
    | r1_tarski(k1_xboole_0,sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15042,c_16505])).

cnf(c_16528,plain,
    ( r1_tarski(k1_xboole_0,sK6)
    | ~ r1_tarski(k1_xboole_0,sK8)
    | ~ v1_relat_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16512])).

cnf(c_11937,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_15502,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_relat_1(sK8)))) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15042,c_11937])).

cnf(c_15699,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_relat_1(sK8)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15502,c_14741,c_14954])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_11953,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15705,plain,
    ( v1_xboole_0(k2_relat_1(sK8)) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_15699,c_11953])).

cnf(c_14750,plain,
    ( v1_relat_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14741])).

cnf(c_11030,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_12855,plain,
    ( X0 != X1
    | sK8 != X1
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_11030])).

cnf(c_14135,plain,
    ( X0 != sK8
    | sK8 = X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_12855])).

cnf(c_14136,plain,
    ( sK8 != sK8
    | sK8 = k1_xboole_0
    | k1_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_14135])).

cnf(c_11029,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12466,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_11029])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12442,plain,
    ( ~ v1_xboole_0(sK8)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12446,plain,
    ( k1_xboole_0 = sK8
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12442])).

cnf(c_147,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_49,plain,
    ( r2_hidden(sK8,k1_funct_2(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23076,c_22045,c_18767,c_18283,c_16820,c_16822,c_16528,c_15705,c_14750,c_14136,c_12466,c_12446,c_147,c_145,c_144,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:48:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.78/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.02  
% 3.78/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/1.02  
% 3.78/1.02  ------  iProver source info
% 3.78/1.02  
% 3.78/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.78/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/1.02  git: non_committed_changes: false
% 3.78/1.02  git: last_make_outside_of_git: false
% 3.78/1.02  
% 3.78/1.02  ------ 
% 3.78/1.02  
% 3.78/1.02  ------ Input Options
% 3.78/1.02  
% 3.78/1.02  --out_options                           all
% 3.78/1.02  --tptp_safe_out                         true
% 3.78/1.02  --problem_path                          ""
% 3.78/1.02  --include_path                          ""
% 3.78/1.02  --clausifier                            res/vclausify_rel
% 3.78/1.02  --clausifier_options                    --mode clausify
% 3.78/1.02  --stdin                                 false
% 3.78/1.02  --stats_out                             all
% 3.78/1.02  
% 3.78/1.02  ------ General Options
% 3.78/1.02  
% 3.78/1.02  --fof                                   false
% 3.78/1.02  --time_out_real                         305.
% 3.78/1.02  --time_out_virtual                      -1.
% 3.78/1.02  --symbol_type_check                     false
% 3.78/1.02  --clausify_out                          false
% 3.78/1.02  --sig_cnt_out                           false
% 3.78/1.02  --trig_cnt_out                          false
% 3.78/1.02  --trig_cnt_out_tolerance                1.
% 3.78/1.02  --trig_cnt_out_sk_spl                   false
% 3.78/1.02  --abstr_cl_out                          false
% 3.78/1.02  
% 3.78/1.02  ------ Global Options
% 3.78/1.02  
% 3.78/1.02  --schedule                              default
% 3.78/1.02  --add_important_lit                     false
% 3.78/1.02  --prop_solver_per_cl                    1000
% 3.78/1.02  --min_unsat_core                        false
% 3.78/1.02  --soft_assumptions                      false
% 3.78/1.02  --soft_lemma_size                       3
% 3.78/1.02  --prop_impl_unit_size                   0
% 3.78/1.02  --prop_impl_unit                        []
% 3.78/1.02  --share_sel_clauses                     true
% 3.78/1.02  --reset_solvers                         false
% 3.78/1.02  --bc_imp_inh                            [conj_cone]
% 3.78/1.02  --conj_cone_tolerance                   3.
% 3.78/1.02  --extra_neg_conj                        none
% 3.78/1.02  --large_theory_mode                     true
% 3.78/1.02  --prolific_symb_bound                   200
% 3.78/1.02  --lt_threshold                          2000
% 3.78/1.02  --clause_weak_htbl                      true
% 3.78/1.02  --gc_record_bc_elim                     false
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing Options
% 3.78/1.02  
% 3.78/1.02  --preprocessing_flag                    true
% 3.78/1.02  --time_out_prep_mult                    0.1
% 3.78/1.02  --splitting_mode                        input
% 3.78/1.02  --splitting_grd                         true
% 3.78/1.02  --splitting_cvd                         false
% 3.78/1.02  --splitting_cvd_svl                     false
% 3.78/1.02  --splitting_nvd                         32
% 3.78/1.02  --sub_typing                            true
% 3.78/1.02  --prep_gs_sim                           true
% 3.78/1.02  --prep_unflatten                        true
% 3.78/1.02  --prep_res_sim                          true
% 3.78/1.02  --prep_upred                            true
% 3.78/1.02  --prep_sem_filter                       exhaustive
% 3.78/1.02  --prep_sem_filter_out                   false
% 3.78/1.02  --pred_elim                             true
% 3.78/1.02  --res_sim_input                         true
% 3.78/1.02  --eq_ax_congr_red                       true
% 3.78/1.02  --pure_diseq_elim                       true
% 3.78/1.02  --brand_transform                       false
% 3.78/1.02  --non_eq_to_eq                          false
% 3.78/1.02  --prep_def_merge                        true
% 3.78/1.02  --prep_def_merge_prop_impl              false
% 3.78/1.02  --prep_def_merge_mbd                    true
% 3.78/1.02  --prep_def_merge_tr_red                 false
% 3.78/1.02  --prep_def_merge_tr_cl                  false
% 3.78/1.02  --smt_preprocessing                     true
% 3.78/1.02  --smt_ac_axioms                         fast
% 3.78/1.02  --preprocessed_out                      false
% 3.78/1.02  --preprocessed_stats                    false
% 3.78/1.02  
% 3.78/1.02  ------ Abstraction refinement Options
% 3.78/1.02  
% 3.78/1.02  --abstr_ref                             []
% 3.78/1.02  --abstr_ref_prep                        false
% 3.78/1.02  --abstr_ref_until_sat                   false
% 3.78/1.02  --abstr_ref_sig_restrict                funpre
% 3.78/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/1.02  --abstr_ref_under                       []
% 3.78/1.02  
% 3.78/1.02  ------ SAT Options
% 3.78/1.02  
% 3.78/1.02  --sat_mode                              false
% 3.78/1.02  --sat_fm_restart_options                ""
% 3.78/1.02  --sat_gr_def                            false
% 3.78/1.02  --sat_epr_types                         true
% 3.78/1.02  --sat_non_cyclic_types                  false
% 3.78/1.02  --sat_finite_models                     false
% 3.78/1.02  --sat_fm_lemmas                         false
% 3.78/1.02  --sat_fm_prep                           false
% 3.78/1.02  --sat_fm_uc_incr                        true
% 3.78/1.02  --sat_out_model                         small
% 3.78/1.02  --sat_out_clauses                       false
% 3.78/1.02  
% 3.78/1.02  ------ QBF Options
% 3.78/1.02  
% 3.78/1.02  --qbf_mode                              false
% 3.78/1.02  --qbf_elim_univ                         false
% 3.78/1.02  --qbf_dom_inst                          none
% 3.78/1.02  --qbf_dom_pre_inst                      false
% 3.78/1.02  --qbf_sk_in                             false
% 3.78/1.02  --qbf_pred_elim                         true
% 3.78/1.02  --qbf_split                             512
% 3.78/1.02  
% 3.78/1.02  ------ BMC1 Options
% 3.78/1.02  
% 3.78/1.02  --bmc1_incremental                      false
% 3.78/1.02  --bmc1_axioms                           reachable_all
% 3.78/1.02  --bmc1_min_bound                        0
% 3.78/1.02  --bmc1_max_bound                        -1
% 3.78/1.02  --bmc1_max_bound_default                -1
% 3.78/1.02  --bmc1_symbol_reachability              true
% 3.78/1.02  --bmc1_property_lemmas                  false
% 3.78/1.02  --bmc1_k_induction                      false
% 3.78/1.02  --bmc1_non_equiv_states                 false
% 3.78/1.02  --bmc1_deadlock                         false
% 3.78/1.02  --bmc1_ucm                              false
% 3.78/1.02  --bmc1_add_unsat_core                   none
% 3.78/1.02  --bmc1_unsat_core_children              false
% 3.78/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/1.02  --bmc1_out_stat                         full
% 3.78/1.02  --bmc1_ground_init                      false
% 3.78/1.02  --bmc1_pre_inst_next_state              false
% 3.78/1.02  --bmc1_pre_inst_state                   false
% 3.78/1.02  --bmc1_pre_inst_reach_state             false
% 3.78/1.02  --bmc1_out_unsat_core                   false
% 3.78/1.02  --bmc1_aig_witness_out                  false
% 3.78/1.02  --bmc1_verbose                          false
% 3.78/1.02  --bmc1_dump_clauses_tptp                false
% 3.78/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.78/1.02  --bmc1_dump_file                        -
% 3.78/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.78/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.78/1.02  --bmc1_ucm_extend_mode                  1
% 3.78/1.02  --bmc1_ucm_init_mode                    2
% 3.78/1.02  --bmc1_ucm_cone_mode                    none
% 3.78/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.78/1.02  --bmc1_ucm_relax_model                  4
% 3.78/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.78/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/1.02  --bmc1_ucm_layered_model                none
% 3.78/1.02  --bmc1_ucm_max_lemma_size               10
% 3.78/1.02  
% 3.78/1.02  ------ AIG Options
% 3.78/1.02  
% 3.78/1.02  --aig_mode                              false
% 3.78/1.02  
% 3.78/1.02  ------ Instantiation Options
% 3.78/1.02  
% 3.78/1.02  --instantiation_flag                    true
% 3.78/1.02  --inst_sos_flag                         false
% 3.78/1.02  --inst_sos_phase                        true
% 3.78/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/1.02  --inst_lit_sel_side                     num_symb
% 3.78/1.02  --inst_solver_per_active                1400
% 3.78/1.02  --inst_solver_calls_frac                1.
% 3.78/1.02  --inst_passive_queue_type               priority_queues
% 3.78/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/1.02  --inst_passive_queues_freq              [25;2]
% 3.78/1.02  --inst_dismatching                      true
% 3.78/1.02  --inst_eager_unprocessed_to_passive     true
% 3.78/1.02  --inst_prop_sim_given                   true
% 3.78/1.02  --inst_prop_sim_new                     false
% 3.78/1.02  --inst_subs_new                         false
% 3.78/1.02  --inst_eq_res_simp                      false
% 3.78/1.02  --inst_subs_given                       false
% 3.78/1.02  --inst_orphan_elimination               true
% 3.78/1.02  --inst_learning_loop_flag               true
% 3.78/1.02  --inst_learning_start                   3000
% 3.78/1.02  --inst_learning_factor                  2
% 3.78/1.02  --inst_start_prop_sim_after_learn       3
% 3.78/1.02  --inst_sel_renew                        solver
% 3.78/1.02  --inst_lit_activity_flag                true
% 3.78/1.02  --inst_restr_to_given                   false
% 3.78/1.02  --inst_activity_threshold               500
% 3.78/1.02  --inst_out_proof                        true
% 3.78/1.02  
% 3.78/1.02  ------ Resolution Options
% 3.78/1.02  
% 3.78/1.02  --resolution_flag                       true
% 3.78/1.02  --res_lit_sel                           adaptive
% 3.78/1.02  --res_lit_sel_side                      none
% 3.78/1.02  --res_ordering                          kbo
% 3.78/1.02  --res_to_prop_solver                    active
% 3.78/1.02  --res_prop_simpl_new                    false
% 3.78/1.02  --res_prop_simpl_given                  true
% 3.78/1.02  --res_passive_queue_type                priority_queues
% 3.78/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/1.02  --res_passive_queues_freq               [15;5]
% 3.78/1.02  --res_forward_subs                      full
% 3.78/1.02  --res_backward_subs                     full
% 3.78/1.02  --res_forward_subs_resolution           true
% 3.78/1.02  --res_backward_subs_resolution          true
% 3.78/1.02  --res_orphan_elimination                true
% 3.78/1.02  --res_time_limit                        2.
% 3.78/1.02  --res_out_proof                         true
% 3.78/1.02  
% 3.78/1.02  ------ Superposition Options
% 3.78/1.02  
% 3.78/1.02  --superposition_flag                    true
% 3.78/1.02  --sup_passive_queue_type                priority_queues
% 3.78/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.78/1.02  --demod_completeness_check              fast
% 3.78/1.02  --demod_use_ground                      true
% 3.78/1.02  --sup_to_prop_solver                    passive
% 3.78/1.02  --sup_prop_simpl_new                    true
% 3.78/1.02  --sup_prop_simpl_given                  true
% 3.78/1.02  --sup_fun_splitting                     false
% 3.78/1.02  --sup_smt_interval                      50000
% 3.78/1.02  
% 3.78/1.02  ------ Superposition Simplification Setup
% 3.78/1.02  
% 3.78/1.02  --sup_indices_passive                   []
% 3.78/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/1.02  --sup_full_bw                           [BwDemod]
% 3.78/1.02  --sup_immed_triv                        [TrivRules]
% 3.78/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/1.02  --sup_immed_bw_main                     []
% 3.78/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/1.02  
% 3.78/1.02  ------ Combination Options
% 3.78/1.02  
% 3.78/1.02  --comb_res_mult                         3
% 3.78/1.02  --comb_sup_mult                         2
% 3.78/1.02  --comb_inst_mult                        10
% 3.78/1.02  
% 3.78/1.02  ------ Debug Options
% 3.78/1.02  
% 3.78/1.02  --dbg_backtrace                         false
% 3.78/1.02  --dbg_dump_prop_clauses                 false
% 3.78/1.02  --dbg_dump_prop_clauses_file            -
% 3.78/1.02  --dbg_out_stat                          false
% 3.78/1.02  ------ Parsing...
% 3.78/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  ------ Proving...
% 3.78/1.02  ------ Problem Properties 
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  clauses                                 44
% 3.78/1.02  conjectures                             1
% 3.78/1.02  EPR                                     5
% 3.78/1.02  Horn                                    35
% 3.78/1.02  unary                                   9
% 3.78/1.02  binary                                  8
% 3.78/1.02  lits                                    121
% 3.78/1.02  lits eq                                 21
% 3.78/1.02  fd_pure                                 0
% 3.78/1.02  fd_pseudo                               0
% 3.78/1.02  fd_cond                                 2
% 3.78/1.02  fd_pseudo_cond                          2
% 3.78/1.02  AC symbols                              0
% 3.78/1.02  
% 3.78/1.02  ------ Schedule dynamic 5 is on 
% 3.78/1.02  
% 3.78/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ 
% 3.78/1.02  Current options:
% 3.78/1.02  ------ 
% 3.78/1.02  
% 3.78/1.02  ------ Input Options
% 3.78/1.02  
% 3.78/1.02  --out_options                           all
% 3.78/1.02  --tptp_safe_out                         true
% 3.78/1.02  --problem_path                          ""
% 3.78/1.02  --include_path                          ""
% 3.78/1.02  --clausifier                            res/vclausify_rel
% 3.78/1.02  --clausifier_options                    --mode clausify
% 3.78/1.02  --stdin                                 false
% 3.78/1.02  --stats_out                             all
% 3.78/1.02  
% 3.78/1.02  ------ General Options
% 3.78/1.02  
% 3.78/1.02  --fof                                   false
% 3.78/1.02  --time_out_real                         305.
% 3.78/1.02  --time_out_virtual                      -1.
% 3.78/1.02  --symbol_type_check                     false
% 3.78/1.02  --clausify_out                          false
% 3.78/1.02  --sig_cnt_out                           false
% 3.78/1.02  --trig_cnt_out                          false
% 3.78/1.02  --trig_cnt_out_tolerance                1.
% 3.78/1.02  --trig_cnt_out_sk_spl                   false
% 3.78/1.02  --abstr_cl_out                          false
% 3.78/1.02  
% 3.78/1.02  ------ Global Options
% 3.78/1.02  
% 3.78/1.02  --schedule                              default
% 3.78/1.02  --add_important_lit                     false
% 3.78/1.02  --prop_solver_per_cl                    1000
% 3.78/1.02  --min_unsat_core                        false
% 3.78/1.02  --soft_assumptions                      false
% 3.78/1.02  --soft_lemma_size                       3
% 3.78/1.02  --prop_impl_unit_size                   0
% 3.78/1.02  --prop_impl_unit                        []
% 3.78/1.02  --share_sel_clauses                     true
% 3.78/1.02  --reset_solvers                         false
% 3.78/1.02  --bc_imp_inh                            [conj_cone]
% 3.78/1.02  --conj_cone_tolerance                   3.
% 3.78/1.02  --extra_neg_conj                        none
% 3.78/1.02  --large_theory_mode                     true
% 3.78/1.02  --prolific_symb_bound                   200
% 3.78/1.02  --lt_threshold                          2000
% 3.78/1.02  --clause_weak_htbl                      true
% 3.78/1.02  --gc_record_bc_elim                     false
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing Options
% 3.78/1.02  
% 3.78/1.02  --preprocessing_flag                    true
% 3.78/1.02  --time_out_prep_mult                    0.1
% 3.78/1.02  --splitting_mode                        input
% 3.78/1.02  --splitting_grd                         true
% 3.78/1.02  --splitting_cvd                         false
% 3.78/1.02  --splitting_cvd_svl                     false
% 3.78/1.02  --splitting_nvd                         32
% 3.78/1.02  --sub_typing                            true
% 3.78/1.02  --prep_gs_sim                           true
% 3.78/1.02  --prep_unflatten                        true
% 3.78/1.02  --prep_res_sim                          true
% 3.78/1.02  --prep_upred                            true
% 3.78/1.02  --prep_sem_filter                       exhaustive
% 3.78/1.02  --prep_sem_filter_out                   false
% 3.78/1.02  --pred_elim                             true
% 3.78/1.02  --res_sim_input                         true
% 3.78/1.02  --eq_ax_congr_red                       true
% 3.78/1.02  --pure_diseq_elim                       true
% 3.78/1.02  --brand_transform                       false
% 3.78/1.02  --non_eq_to_eq                          false
% 3.78/1.02  --prep_def_merge                        true
% 3.78/1.02  --prep_def_merge_prop_impl              false
% 3.78/1.02  --prep_def_merge_mbd                    true
% 3.78/1.02  --prep_def_merge_tr_red                 false
% 3.78/1.02  --prep_def_merge_tr_cl                  false
% 3.78/1.02  --smt_preprocessing                     true
% 3.78/1.02  --smt_ac_axioms                         fast
% 3.78/1.02  --preprocessed_out                      false
% 3.78/1.02  --preprocessed_stats                    false
% 3.78/1.02  
% 3.78/1.02  ------ Abstraction refinement Options
% 3.78/1.02  
% 3.78/1.02  --abstr_ref                             []
% 3.78/1.02  --abstr_ref_prep                        false
% 3.78/1.02  --abstr_ref_until_sat                   false
% 3.78/1.02  --abstr_ref_sig_restrict                funpre
% 3.78/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/1.02  --abstr_ref_under                       []
% 3.78/1.02  
% 3.78/1.02  ------ SAT Options
% 3.78/1.02  
% 3.78/1.02  --sat_mode                              false
% 3.78/1.02  --sat_fm_restart_options                ""
% 3.78/1.02  --sat_gr_def                            false
% 3.78/1.02  --sat_epr_types                         true
% 3.78/1.02  --sat_non_cyclic_types                  false
% 3.78/1.02  --sat_finite_models                     false
% 3.78/1.02  --sat_fm_lemmas                         false
% 3.78/1.02  --sat_fm_prep                           false
% 3.78/1.02  --sat_fm_uc_incr                        true
% 3.78/1.02  --sat_out_model                         small
% 3.78/1.02  --sat_out_clauses                       false
% 3.78/1.02  
% 3.78/1.02  ------ QBF Options
% 3.78/1.02  
% 3.78/1.02  --qbf_mode                              false
% 3.78/1.02  --qbf_elim_univ                         false
% 3.78/1.02  --qbf_dom_inst                          none
% 3.78/1.02  --qbf_dom_pre_inst                      false
% 3.78/1.02  --qbf_sk_in                             false
% 3.78/1.02  --qbf_pred_elim                         true
% 3.78/1.02  --qbf_split                             512
% 3.78/1.02  
% 3.78/1.02  ------ BMC1 Options
% 3.78/1.02  
% 3.78/1.02  --bmc1_incremental                      false
% 3.78/1.02  --bmc1_axioms                           reachable_all
% 3.78/1.02  --bmc1_min_bound                        0
% 3.78/1.02  --bmc1_max_bound                        -1
% 3.78/1.02  --bmc1_max_bound_default                -1
% 3.78/1.02  --bmc1_symbol_reachability              true
% 3.78/1.02  --bmc1_property_lemmas                  false
% 3.78/1.02  --bmc1_k_induction                      false
% 3.78/1.02  --bmc1_non_equiv_states                 false
% 3.78/1.02  --bmc1_deadlock                         false
% 3.78/1.02  --bmc1_ucm                              false
% 3.78/1.02  --bmc1_add_unsat_core                   none
% 3.78/1.02  --bmc1_unsat_core_children              false
% 3.78/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/1.02  --bmc1_out_stat                         full
% 3.78/1.02  --bmc1_ground_init                      false
% 3.78/1.02  --bmc1_pre_inst_next_state              false
% 3.78/1.02  --bmc1_pre_inst_state                   false
% 3.78/1.02  --bmc1_pre_inst_reach_state             false
% 3.78/1.02  --bmc1_out_unsat_core                   false
% 3.78/1.02  --bmc1_aig_witness_out                  false
% 3.78/1.02  --bmc1_verbose                          false
% 3.78/1.02  --bmc1_dump_clauses_tptp                false
% 3.78/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.78/1.02  --bmc1_dump_file                        -
% 3.78/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.78/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.78/1.02  --bmc1_ucm_extend_mode                  1
% 3.78/1.02  --bmc1_ucm_init_mode                    2
% 3.78/1.02  --bmc1_ucm_cone_mode                    none
% 3.78/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.78/1.02  --bmc1_ucm_relax_model                  4
% 3.78/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.78/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/1.02  --bmc1_ucm_layered_model                none
% 3.78/1.02  --bmc1_ucm_max_lemma_size               10
% 3.78/1.02  
% 3.78/1.02  ------ AIG Options
% 3.78/1.02  
% 3.78/1.02  --aig_mode                              false
% 3.78/1.02  
% 3.78/1.02  ------ Instantiation Options
% 3.78/1.02  
% 3.78/1.02  --instantiation_flag                    true
% 3.78/1.02  --inst_sos_flag                         false
% 3.78/1.02  --inst_sos_phase                        true
% 3.78/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/1.02  --inst_lit_sel_side                     none
% 3.78/1.02  --inst_solver_per_active                1400
% 3.78/1.02  --inst_solver_calls_frac                1.
% 3.78/1.02  --inst_passive_queue_type               priority_queues
% 3.78/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/1.02  --inst_passive_queues_freq              [25;2]
% 3.78/1.02  --inst_dismatching                      true
% 3.78/1.02  --inst_eager_unprocessed_to_passive     true
% 3.78/1.02  --inst_prop_sim_given                   true
% 3.78/1.02  --inst_prop_sim_new                     false
% 3.78/1.02  --inst_subs_new                         false
% 3.78/1.02  --inst_eq_res_simp                      false
% 3.78/1.02  --inst_subs_given                       false
% 3.78/1.02  --inst_orphan_elimination               true
% 3.78/1.02  --inst_learning_loop_flag               true
% 3.78/1.02  --inst_learning_start                   3000
% 3.78/1.02  --inst_learning_factor                  2
% 3.78/1.02  --inst_start_prop_sim_after_learn       3
% 3.78/1.02  --inst_sel_renew                        solver
% 3.78/1.02  --inst_lit_activity_flag                true
% 3.78/1.02  --inst_restr_to_given                   false
% 3.78/1.02  --inst_activity_threshold               500
% 3.78/1.02  --inst_out_proof                        true
% 3.78/1.02  
% 3.78/1.02  ------ Resolution Options
% 3.78/1.02  
% 3.78/1.02  --resolution_flag                       false
% 3.78/1.02  --res_lit_sel                           adaptive
% 3.78/1.02  --res_lit_sel_side                      none
% 3.78/1.02  --res_ordering                          kbo
% 3.78/1.02  --res_to_prop_solver                    active
% 3.78/1.02  --res_prop_simpl_new                    false
% 3.78/1.02  --res_prop_simpl_given                  true
% 3.78/1.02  --res_passive_queue_type                priority_queues
% 3.78/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/1.02  --res_passive_queues_freq               [15;5]
% 3.78/1.02  --res_forward_subs                      full
% 3.78/1.02  --res_backward_subs                     full
% 3.78/1.02  --res_forward_subs_resolution           true
% 3.78/1.02  --res_backward_subs_resolution          true
% 3.78/1.02  --res_orphan_elimination                true
% 3.78/1.02  --res_time_limit                        2.
% 3.78/1.02  --res_out_proof                         true
% 3.78/1.02  
% 3.78/1.02  ------ Superposition Options
% 3.78/1.02  
% 3.78/1.02  --superposition_flag                    true
% 3.78/1.02  --sup_passive_queue_type                priority_queues
% 3.78/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.78/1.02  --demod_completeness_check              fast
% 3.78/1.02  --demod_use_ground                      true
% 3.78/1.02  --sup_to_prop_solver                    passive
% 3.78/1.02  --sup_prop_simpl_new                    true
% 3.78/1.02  --sup_prop_simpl_given                  true
% 3.78/1.02  --sup_fun_splitting                     false
% 3.78/1.02  --sup_smt_interval                      50000
% 3.78/1.02  
% 3.78/1.02  ------ Superposition Simplification Setup
% 3.78/1.02  
% 3.78/1.02  --sup_indices_passive                   []
% 3.78/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.78/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/1.02  --sup_full_bw                           [BwDemod]
% 3.78/1.02  --sup_immed_triv                        [TrivRules]
% 3.78/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/1.02  --sup_immed_bw_main                     []
% 3.78/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.78/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.78/1.02  
% 3.78/1.02  ------ Combination Options
% 3.78/1.02  
% 3.78/1.02  --comb_res_mult                         3
% 3.78/1.02  --comb_sup_mult                         2
% 3.78/1.02  --comb_inst_mult                        10
% 3.78/1.02  
% 3.78/1.02  ------ Debug Options
% 3.78/1.02  
% 3.78/1.02  --dbg_backtrace                         false
% 3.78/1.02  --dbg_dump_prop_clauses                 false
% 3.78/1.02  --dbg_dump_prop_clauses_file            -
% 3.78/1.02  --dbg_out_stat                          false
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  % SZS status Theorem for theBenchmark.p
% 3.78/1.02  
% 3.78/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/1.02  
% 3.78/1.02  fof(f18,conjecture,(
% 3.78/1.02    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f19,negated_conjecture,(
% 3.78/1.02    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.78/1.02    inference(negated_conjecture,[],[f18])).
% 3.78/1.02  
% 3.78/1.02  fof(f35,plain,(
% 3.78/1.02    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 3.78/1.02    inference(ennf_transformation,[],[f19])).
% 3.78/1.02  
% 3.78/1.02  fof(f56,plain,(
% 3.78/1.02    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) | ~v1_funct_2(sK8,sK6,sK7) | ~v1_funct_1(sK8)) & r2_hidden(sK8,k1_funct_2(sK6,sK7)))),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f57,plain,(
% 3.78/1.02    (~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) | ~v1_funct_2(sK8,sK6,sK7) | ~v1_funct_1(sK8)) & r2_hidden(sK8,k1_funct_2(sK6,sK7))),
% 3.78/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f56])).
% 3.78/1.02  
% 3.78/1.02  fof(f105,plain,(
% 3.78/1.02    r2_hidden(sK8,k1_funct_2(sK6,sK7))),
% 3.78/1.02    inference(cnf_transformation,[],[f57])).
% 3.78/1.02  
% 3.78/1.02  fof(f15,axiom,(
% 3.78/1.02    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f36,plain,(
% 3.78/1.02    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.78/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.78/1.02  
% 3.78/1.02  fof(f37,plain,(
% 3.78/1.02    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.78/1.02    inference(definition_folding,[],[f15,f36])).
% 3.78/1.02  
% 3.78/1.02  fof(f53,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 3.78/1.02    inference(nnf_transformation,[],[f37])).
% 3.78/1.02  
% 3.78/1.02  fof(f94,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 3.78/1.02    inference(cnf_transformation,[],[f53])).
% 3.78/1.02  
% 3.78/1.02  fof(f114,plain,(
% 3.78/1.02    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 3.78/1.02    inference(equality_resolution,[],[f94])).
% 3.78/1.02  
% 3.78/1.02  fof(f47,plain,(
% 3.78/1.02    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.78/1.02    inference(nnf_transformation,[],[f36])).
% 3.78/1.02  
% 3.78/1.02  fof(f48,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.78/1.02    inference(rectify,[],[f47])).
% 3.78/1.02  
% 3.78/1.02  fof(f51,plain,(
% 3.78/1.02    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) & k1_relat_1(sK4(X0,X1,X6)) = X1 & sK4(X0,X1,X6) = X6 & v1_funct_1(sK4(X0,X1,X6)) & v1_relat_1(sK4(X0,X1,X6))))),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f50,plain,(
% 3.78/1.02    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0) & k1_relat_1(sK3(X0,X1,X2)) = X1 & sK3(X0,X1,X2) = X3 & v1_funct_1(sK3(X0,X1,X2)) & v1_relat_1(sK3(X0,X1,X2))))) )),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f49,plain,(
% 3.78/1.02    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK2(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK2(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f52,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK2(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0) & k1_relat_1(sK3(X0,X1,X2)) = X1 & sK2(X0,X1,X2) = sK3(X0,X1,X2) & v1_funct_1(sK3(X0,X1,X2)) & v1_relat_1(sK3(X0,X1,X2))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) & k1_relat_1(sK4(X0,X1,X6)) = X1 & sK4(X0,X1,X6) = X6 & v1_funct_1(sK4(X0,X1,X6)) & v1_relat_1(sK4(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.78/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f51,f50,f49])).
% 3.78/1.02  
% 3.78/1.02  fof(f84,plain,(
% 3.78/1.02    ( ! [X6,X2,X0,X1] : (sK4(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f52])).
% 3.78/1.02  
% 3.78/1.02  fof(f86,plain,(
% 3.78/1.02    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f52])).
% 3.78/1.02  
% 3.78/1.02  fof(f12,axiom,(
% 3.78/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f25,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.78/1.02    inference(ennf_transformation,[],[f12])).
% 3.78/1.02  
% 3.78/1.02  fof(f26,plain,(
% 3.78/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.78/1.02    inference(flattening,[],[f25])).
% 3.78/1.02  
% 3.78/1.02  fof(f77,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f26])).
% 3.78/1.02  
% 3.78/1.02  fof(f85,plain,(
% 3.78/1.02    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK4(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f52])).
% 3.78/1.02  
% 3.78/1.02  fof(f14,axiom,(
% 3.78/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f29,plain,(
% 3.78/1.02    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.78/1.02    inference(ennf_transformation,[],[f14])).
% 3.78/1.02  
% 3.78/1.02  fof(f30,plain,(
% 3.78/1.02    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.78/1.02    inference(flattening,[],[f29])).
% 3.78/1.02  
% 3.78/1.02  fof(f81,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f30])).
% 3.78/1.02  
% 3.78/1.02  fof(f16,axiom,(
% 3.78/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f31,plain,(
% 3.78/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.78/1.02    inference(ennf_transformation,[],[f16])).
% 3.78/1.02  
% 3.78/1.02  fof(f32,plain,(
% 3.78/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.78/1.02    inference(flattening,[],[f31])).
% 3.78/1.02  
% 3.78/1.02  fof(f97,plain,(
% 3.78/1.02    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f32])).
% 3.78/1.02  
% 3.78/1.02  fof(f98,plain,(
% 3.78/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f32])).
% 3.78/1.02  
% 3.78/1.02  fof(f13,axiom,(
% 3.78/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f27,plain,(
% 3.78/1.02    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/1.02    inference(ennf_transformation,[],[f13])).
% 3.78/1.02  
% 3.78/1.02  fof(f28,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/1.02    inference(flattening,[],[f27])).
% 3.78/1.02  
% 3.78/1.02  fof(f79,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/1.02    inference(cnf_transformation,[],[f28])).
% 3.78/1.02  
% 3.78/1.02  fof(f106,plain,(
% 3.78/1.02    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) | ~v1_funct_2(sK8,sK6,sK7) | ~v1_funct_1(sK8)),
% 3.78/1.02    inference(cnf_transformation,[],[f57])).
% 3.78/1.02  
% 3.78/1.02  fof(f10,axiom,(
% 3.78/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f23,plain,(
% 3.78/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/1.02    inference(ennf_transformation,[],[f10])).
% 3.78/1.02  
% 3.78/1.02  fof(f75,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/1.02    inference(cnf_transformation,[],[f23])).
% 3.78/1.02  
% 3.78/1.02  fof(f82,plain,(
% 3.78/1.02    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK4(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f52])).
% 3.78/1.02  
% 3.78/1.02  fof(f83,plain,(
% 3.78/1.02    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK4(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f52])).
% 3.78/1.02  
% 3.78/1.02  fof(f4,axiom,(
% 3.78/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f42,plain,(
% 3.78/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/1.02    inference(nnf_transformation,[],[f4])).
% 3.78/1.02  
% 3.78/1.02  fof(f43,plain,(
% 3.78/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/1.02    inference(flattening,[],[f42])).
% 3.78/1.02  
% 3.78/1.02  fof(f63,plain,(
% 3.78/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.78/1.02    inference(cnf_transformation,[],[f43])).
% 3.78/1.02  
% 3.78/1.02  fof(f107,plain,(
% 3.78/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.78/1.02    inference(equality_resolution,[],[f63])).
% 3.78/1.02  
% 3.78/1.02  fof(f9,axiom,(
% 3.78/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f73,plain,(
% 3.78/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.78/1.02    inference(cnf_transformation,[],[f9])).
% 3.78/1.02  
% 3.78/1.02  fof(f8,axiom,(
% 3.78/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f21,plain,(
% 3.78/1.02    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.78/1.02    inference(ennf_transformation,[],[f8])).
% 3.78/1.02  
% 3.78/1.02  fof(f22,plain,(
% 3.78/1.02    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.78/1.02    inference(flattening,[],[f21])).
% 3.78/1.02  
% 3.78/1.02  fof(f71,plain,(
% 3.78/1.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f22])).
% 3.78/1.02  
% 3.78/1.02  fof(f64,plain,(
% 3.78/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f43])).
% 3.78/1.02  
% 3.78/1.02  fof(f5,axiom,(
% 3.78/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f44,plain,(
% 3.78/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.78/1.02    inference(nnf_transformation,[],[f5])).
% 3.78/1.02  
% 3.78/1.02  fof(f45,plain,(
% 3.78/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.78/1.02    inference(flattening,[],[f44])).
% 3.78/1.02  
% 3.78/1.02  fof(f65,plain,(
% 3.78/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f45])).
% 3.78/1.02  
% 3.78/1.02  fof(f66,plain,(
% 3.78/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.78/1.02    inference(cnf_transformation,[],[f45])).
% 3.78/1.02  
% 3.78/1.02  fof(f110,plain,(
% 3.78/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.78/1.02    inference(equality_resolution,[],[f66])).
% 3.78/1.02  
% 3.78/1.02  fof(f62,plain,(
% 3.78/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.78/1.02    inference(cnf_transformation,[],[f43])).
% 3.78/1.02  
% 3.78/1.02  fof(f108,plain,(
% 3.78/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.78/1.02    inference(equality_resolution,[],[f62])).
% 3.78/1.02  
% 3.78/1.02  fof(f2,axiom,(
% 3.78/1.02    v1_xboole_0(k1_xboole_0)),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f60,plain,(
% 3.78/1.02    v1_xboole_0(k1_xboole_0)),
% 3.78/1.02    inference(cnf_transformation,[],[f2])).
% 3.78/1.02  
% 3.78/1.02  fof(f6,axiom,(
% 3.78/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f46,plain,(
% 3.78/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.78/1.02    inference(nnf_transformation,[],[f6])).
% 3.78/1.02  
% 3.78/1.02  fof(f69,plain,(
% 3.78/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f46])).
% 3.78/1.02  
% 3.78/1.02  fof(f17,axiom,(
% 3.78/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f33,plain,(
% 3.78/1.02    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.78/1.02    inference(ennf_transformation,[],[f17])).
% 3.78/1.02  
% 3.78/1.02  fof(f34,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.78/1.02    inference(flattening,[],[f33])).
% 3.78/1.02  
% 3.78/1.02  fof(f54,plain,(
% 3.78/1.02    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)))),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f55,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.78/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f54])).
% 3.78/1.02  
% 3.78/1.02  fof(f101,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK5(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f55])).
% 3.78/1.02  
% 3.78/1.02  fof(f118,plain,(
% 3.78/1.02    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/1.02    inference(equality_resolution,[],[f101])).
% 3.78/1.02  
% 3.78/1.02  fof(f103,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK5(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f55])).
% 3.78/1.02  
% 3.78/1.02  fof(f116,plain,(
% 3.78/1.02    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.78/1.02    inference(equality_resolution,[],[f103])).
% 3.78/1.02  
% 3.78/1.02  fof(f1,axiom,(
% 3.78/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f38,plain,(
% 3.78/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.78/1.02    inference(nnf_transformation,[],[f1])).
% 3.78/1.02  
% 3.78/1.02  fof(f39,plain,(
% 3.78/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/1.02    inference(rectify,[],[f38])).
% 3.78/1.02  
% 3.78/1.02  fof(f40,plain,(
% 3.78/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f41,plain,(
% 3.78/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f58,plain,(
% 3.78/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f41])).
% 3.78/1.02  
% 3.78/1.02  fof(f11,axiom,(
% 3.78/1.02    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f24,plain,(
% 3.78/1.02    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.78/1.02    inference(ennf_transformation,[],[f11])).
% 3.78/1.02  
% 3.78/1.02  fof(f76,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f24])).
% 3.78/1.02  
% 3.78/1.02  fof(f3,axiom,(
% 3.78/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.78/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f20,plain,(
% 3.78/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.78/1.02    inference(ennf_transformation,[],[f3])).
% 3.78/1.02  
% 3.78/1.02  fof(f61,plain,(
% 3.78/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f20])).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11033,plain,
% 3.78/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.78/1.02      theory(equality) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_23074,plain,
% 3.78/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(sK8,X2) | X2 != X1 | sK8 != X0 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_11033]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_23076,plain,
% 3.78/1.02      ( r1_tarski(sK8,k1_xboole_0)
% 3.78/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.78/1.02      | sK8 != k1_xboole_0
% 3.78/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_23074]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_48,negated_conjecture,
% 3.78/1.02      ( r2_hidden(sK8,k1_funct_2(sK6,sK7)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f105]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11934,plain,
% 3.78/1.02      ( r2_hidden(sK8,k1_funct_2(sK6,sK7)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_37,plain,
% 3.78/1.02      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f114]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11938,plain,
% 3.78/1.02      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_33,plain,
% 3.78/1.02      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK4(X0,X1,X3) = X3 ),
% 3.78/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11942,plain,
% 3.78/1.02      ( sK4(X0,X1,X2) = X2
% 3.78/1.02      | sP0(X0,X1,X3) != iProver_top
% 3.78/1.02      | r2_hidden(X2,X3) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_13746,plain,
% 3.78/1.02      ( sK4(X0,X1,X2) = X2
% 3.78/1.02      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11938,c_11942]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_13934,plain,
% 3.78/1.02      ( sK4(sK7,sK6,sK8) = sK8 ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11934,c_13746]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_31,plain,
% 3.78/1.02      ( ~ sP0(X0,X1,X2)
% 3.78/1.02      | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0)
% 3.78/1.02      | ~ r2_hidden(X3,X2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11944,plain,
% 3.78/1.02      ( sP0(X0,X1,X2) != iProver_top
% 3.78/1.02      | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) = iProver_top
% 3.78/1.02      | r2_hidden(X3,X2) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15147,plain,
% 3.78/1.02      ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) = iProver_top
% 3.78/1.02      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11938,c_11944]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_22045,plain,
% 3.78/1.02      ( r1_tarski(k2_relat_1(sK8),sK7) = iProver_top
% 3.78/1.02      | r2_hidden(sK8,k1_funct_2(sK6,sK7)) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_13934,c_15147]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_19,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.78/1.02      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.78/1.02      | ~ v1_relat_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11952,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.78/1.02      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.78/1.02      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.78/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_32,plain,
% 3.78/1.02      ( ~ sP0(X0,X1,X2)
% 3.78/1.02      | ~ r2_hidden(X3,X2)
% 3.78/1.02      | k1_relat_1(sK4(X0,X1,X3)) = X1 ),
% 3.78/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11943,plain,
% 3.78/1.02      ( k1_relat_1(sK4(X0,X1,X2)) = X1
% 3.78/1.02      | sP0(X0,X1,X3) != iProver_top
% 3.78/1.02      | r2_hidden(X2,X3) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14472,plain,
% 3.78/1.02      ( k1_relat_1(sK4(X0,X1,X2)) = X1
% 3.78/1.02      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11938,c_11943]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15040,plain,
% 3.78/1.02      ( k1_relat_1(sK4(sK7,sK6,sK8)) = sK6 ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11934,c_14472]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15042,plain,
% 3.78/1.02      ( k1_relat_1(sK8) = sK6 ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_15040,c_13934]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_22,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/1.02      | v1_partfun1(X0,X1)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | v1_xboole_0(X2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_39,plain,
% 3.78/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_relat_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f97]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_570,plain,
% 3.78/1.02      ( v1_partfun1(X0,X1)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_funct_1(X3)
% 3.78/1.02      | ~ v1_relat_1(X3)
% 3.78/1.02      | v1_xboole_0(X2)
% 3.78/1.02      | X3 != X0
% 3.78/1.02      | k1_relat_1(X3) != X1
% 3.78/1.02      | k2_relat_1(X3) != X2 ),
% 3.78/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_39]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_571,plain,
% 3.78/1.02      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_relat_1(X0)
% 3.78/1.02      | v1_xboole_0(k2_relat_1(X0)) ),
% 3.78/1.02      inference(unflattening,[status(thm)],[c_570]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_38,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_relat_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_575,plain,
% 3.78/1.02      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_relat_1(X0)
% 3.78/1.02      | v1_xboole_0(k2_relat_1(X0)) ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_571,c_38]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_20,plain,
% 3.78/1.02      ( v1_funct_2(X0,X1,X2)
% 3.78/1.02      | ~ v1_partfun1(X0,X1)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ v1_funct_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_47,negated_conjecture,
% 3.78/1.02      ( ~ v1_funct_2(sK8,sK6,sK7)
% 3.78/1.02      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_1(sK8) ),
% 3.78/1.02      inference(cnf_transformation,[],[f106]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_642,plain,
% 3.78/1.02      ( ~ v1_partfun1(X0,X1)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_funct_1(sK8)
% 3.78/1.02      | sK7 != X2
% 3.78/1.02      | sK6 != X1
% 3.78/1.02      | sK8 != X0 ),
% 3.78/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_47]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_643,plain,
% 3.78/1.02      ( ~ v1_partfun1(sK8,sK6)
% 3.78/1.02      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_1(sK8) ),
% 3.78/1.02      inference(unflattening,[status(thm)],[c_642]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_792,plain,
% 3.78/1.02      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_funct_1(sK8)
% 3.78/1.02      | ~ v1_relat_1(X0)
% 3.78/1.02      | v1_xboole_0(k2_relat_1(X0))
% 3.78/1.02      | k1_relat_1(X0) != sK6
% 3.78/1.02      | sK8 != X0 ),
% 3.78/1.02      inference(resolution_lifted,[status(thm)],[c_575,c_643]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_793,plain,
% 3.78/1.02      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_1(sK8)
% 3.78/1.02      | ~ v1_relat_1(sK8)
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8))
% 3.78/1.02      | k1_relat_1(sK8) != sK6 ),
% 3.78/1.02      inference(unflattening,[status(thm)],[c_792]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_17,plain,
% 3.78/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | v1_relat_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_805,plain,
% 3.78/1.02      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_1(sK8)
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8))
% 3.78/1.02      | k1_relat_1(sK8) != sK6 ),
% 3.78/1.02      inference(forward_subsumption_resolution,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_793,c_17]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11927,plain,
% 3.78/1.02      ( k1_relat_1(sK8) != sK6
% 3.78/1.02      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15435,plain,
% 3.78/1.02      ( sK6 != sK6
% 3.78/1.02      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(demodulation,[status(thm)],[c_15042,c_11927]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15473,plain,
% 3.78/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(equality_resolution_simp,[status(thm)],[c_15435]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_794,plain,
% 3.78/1.02      ( k1_relat_1(sK8) != sK6
% 3.78/1.02      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top
% 3.78/1.02      | v1_relat_1(sK8) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_35,plain,
% 3.78/1.02      ( ~ sP0(X0,X1,X2)
% 3.78/1.02      | ~ r2_hidden(X3,X2)
% 3.78/1.02      | v1_relat_1(sK4(X0,X1,X3)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11940,plain,
% 3.78/1.02      ( sP0(X0,X1,X2) != iProver_top
% 3.78/1.02      | r2_hidden(X3,X2) != iProver_top
% 3.78/1.02      | v1_relat_1(sK4(X0,X1,X3)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14350,plain,
% 3.78/1.02      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.78/1.02      | v1_relat_1(sK4(X2,X1,X0)) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11938,c_11940]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14739,plain,
% 3.78/1.02      ( v1_relat_1(sK4(sK7,sK6,sK8)) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11934,c_14350]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14741,plain,
% 3.78/1.02      ( v1_relat_1(sK8) = iProver_top ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_14739,c_13934]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_34,plain,
% 3.78/1.02      ( ~ sP0(X0,X1,X2)
% 3.78/1.02      | ~ r2_hidden(X3,X2)
% 3.78/1.02      | v1_funct_1(sK4(X0,X1,X3)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11941,plain,
% 3.78/1.02      ( sP0(X0,X1,X2) != iProver_top
% 3.78/1.02      | r2_hidden(X3,X2) != iProver_top
% 3.78/1.02      | v1_funct_1(sK4(X0,X1,X3)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14466,plain,
% 3.78/1.02      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.78/1.02      | v1_funct_1(sK4(X2,X1,X0)) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11938,c_11941]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14952,plain,
% 3.78/1.02      ( v1_funct_1(sK4(sK7,sK6,sK8)) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11934,c_14466]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14954,plain,
% 3.78/1.02      ( v1_funct_1(sK8) = iProver_top ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_14952,c_13934]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_17834,plain,
% 3.78/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_15473,c_794,c_14741,c_14954,c_15042]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_18103,plain,
% 3.78/1.02      ( r1_tarski(k1_relat_1(sK8),sK6) != iProver_top
% 3.78/1.02      | r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
% 3.78/1.02      | v1_relat_1(sK8) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11952,c_17834]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_18128,plain,
% 3.78/1.02      ( r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
% 3.78/1.02      | r1_tarski(sK6,sK6) != iProver_top
% 3.78/1.02      | v1_relat_1(sK8) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_18103,c_15042]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_18760,plain,
% 3.78/1.02      ( r1_tarski(sK6,sK6) != iProver_top
% 3.78/1.02      | r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_18128,c_14741]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_18761,plain,
% 3.78/1.02      ( r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
% 3.78/1.02      | r1_tarski(sK6,sK6) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_18760]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5,plain,
% 3.78/1.02      ( r1_tarski(X0,X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f107]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11960,plain,
% 3.78/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_18767,plain,
% 3.78/1.02      ( r1_tarski(k2_relat_1(sK8),sK7) != iProver_top
% 3.78/1.02      | v1_xboole_0(k2_relat_1(sK8)) = iProver_top ),
% 3.78/1.02      inference(forward_subsumption_resolution,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_18761,c_11960]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16,plain,
% 3.78/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.78/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14,plain,
% 3.78/1.02      ( ~ r1_tarski(X0,X1)
% 3.78/1.02      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.78/1.02      | ~ v1_relat_1(X1)
% 3.78/1.02      | ~ v1_relat_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11955,plain,
% 3.78/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.78/1.02      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 3.78/1.02      | v1_relat_1(X0) != iProver_top
% 3.78/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16442,plain,
% 3.78/1.02      ( r1_tarski(sK6,k1_relat_1(X0)) = iProver_top
% 3.78/1.02      | r1_tarski(sK8,X0) != iProver_top
% 3.78/1.02      | v1_relat_1(X0) != iProver_top
% 3.78/1.02      | v1_relat_1(sK8) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_15042,c_11955]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16635,plain,
% 3.78/1.02      ( v1_relat_1(X0) != iProver_top
% 3.78/1.02      | r1_tarski(sK8,X0) != iProver_top
% 3.78/1.02      | r1_tarski(sK6,k1_relat_1(X0)) = iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_16442,c_14741]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16636,plain,
% 3.78/1.02      ( r1_tarski(sK6,k1_relat_1(X0)) = iProver_top
% 3.78/1.02      | r1_tarski(sK8,X0) != iProver_top
% 3.78/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_16635]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_4,plain,
% 3.78/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.78/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11961,plain,
% 3.78/1.02      ( X0 = X1
% 3.78/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.78/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16646,plain,
% 3.78/1.02      ( k1_relat_1(X0) = sK6
% 3.78/1.02      | r1_tarski(k1_relat_1(X0),sK6) != iProver_top
% 3.78/1.02      | r1_tarski(sK8,X0) != iProver_top
% 3.78/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_16636,c_11961]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_17920,plain,
% 3.78/1.02      ( k1_relat_1(k1_xboole_0) = sK6
% 3.78/1.02      | r1_tarski(sK8,k1_xboole_0) != iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,sK6) != iProver_top
% 3.78/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_16,c_16646]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_17926,plain,
% 3.78/1.02      ( sK6 = k1_xboole_0
% 3.78/1.02      | r1_tarski(sK8,k1_xboole_0) != iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,sK6) != iProver_top
% 3.78/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_17920,c_16]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_126,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.78/1.02      | v1_relat_1(X0) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_128,plain,
% 3.78/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.78/1.02      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_126]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_9,plain,
% 3.78/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.78/1.02      | k1_xboole_0 = X0
% 3.78/1.02      | k1_xboole_0 = X1 ),
% 3.78/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_144,plain,
% 3.78/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.78/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_8,plain,
% 3.78/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.78/1.02      inference(cnf_transformation,[],[f110]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_145,plain,
% 3.78/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6,plain,
% 3.78/1.02      ( r1_tarski(X0,X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f108]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_146,plain,
% 3.78/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_148,plain,
% 3.78/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_146]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2,plain,
% 3.78/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_156,plain,
% 3.78/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_10,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.78/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12303,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12304,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.78/1.02      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_12303]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12306,plain,
% 3.78/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_12304]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12501,plain,
% 3.78/1.02      ( ~ r1_tarski(X0,X1)
% 3.78/1.02      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 3.78/1.02      | X2 != X0
% 3.78/1.02      | k2_zfmisc_1(X3,X4) != X1 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_11033]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12502,plain,
% 3.78/1.02      ( X0 != X1
% 3.78/1.02      | k2_zfmisc_1(X2,X3) != X4
% 3.78/1.02      | r1_tarski(X1,X4) != iProver_top
% 3.78/1.02      | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_12501]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12504,plain,
% 3.78/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.78/1.02      | k1_xboole_0 != k1_xboole_0
% 3.78/1.02      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_12502]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11031,plain,
% 3.78/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.78/1.02      theory(equality) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16542,plain,
% 3.78/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_11031]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16543,plain,
% 3.78/1.02      ( sK6 != X0
% 3.78/1.02      | v1_xboole_0(X0) != iProver_top
% 3.78/1.02      | v1_xboole_0(sK6) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_16542]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16545,plain,
% 3.78/1.02      ( sK6 != k1_xboole_0
% 3.78/1.02      | v1_xboole_0(sK6) = iProver_top
% 3.78/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_16543]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_44,plain,
% 3.78/1.02      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.78/1.02      | r2_hidden(sK5(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_relat_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f118]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_674,plain,
% 3.78/1.02      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.78/1.02      | r2_hidden(sK5(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_funct_1(sK8)
% 3.78/1.02      | ~ v1_relat_1(X0)
% 3.78/1.02      | k1_relat_1(X0) != sK6
% 3.78/1.02      | sK7 != X1
% 3.78/1.02      | sK8 != X0 ),
% 3.78/1.02      inference(resolution_lifted,[status(thm)],[c_44,c_47]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_675,plain,
% 3.78/1.02      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.78/1.02      | r2_hidden(sK5(k1_relat_1(sK8),sK7,sK8),k1_relat_1(sK8))
% 3.78/1.02      | ~ v1_funct_1(sK8)
% 3.78/1.02      | ~ v1_relat_1(sK8)
% 3.78/1.02      | k1_relat_1(sK8) != sK6 ),
% 3.78/1.02      inference(unflattening,[status(thm)],[c_674]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_687,plain,
% 3.78/1.02      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 3.78/1.02      | r2_hidden(sK5(k1_relat_1(sK8),sK7,sK8),k1_relat_1(sK8))
% 3.78/1.02      | ~ v1_funct_1(sK8)
% 3.78/1.02      | k1_relat_1(sK8) != sK6 ),
% 3.78/1.02      inference(forward_subsumption_resolution,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_675,c_17]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11932,plain,
% 3.78/1.02      ( k1_relat_1(sK8) != sK6
% 3.78/1.02      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.78/1.02      | r2_hidden(sK5(k1_relat_1(sK8),sK7,sK8),k1_relat_1(sK8)) = iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15439,plain,
% 3.78/1.02      ( sK6 != sK6
% 3.78/1.02      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.78/1.02      | r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top ),
% 3.78/1.02      inference(demodulation,[status(thm)],[c_15042,c_11932]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15448,plain,
% 3.78/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.78/1.02      | r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top ),
% 3.78/1.02      inference(equality_resolution_simp,[status(thm)],[c_15439]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_17853,plain,
% 3.78/1.02      ( r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top
% 3.78/1.02      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_15448,c_14954]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_17854,plain,
% 3.78/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 3.78/1.02      | r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_17853]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_42,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.78/1.02      | r2_hidden(sK5(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_relat_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f116]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11935,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.78/1.02      | r2_hidden(sK5(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
% 3.78/1.02      | v1_funct_1(X0) != iProver_top
% 3.78/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15504,plain,
% 3.78/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),X0))) = iProver_top
% 3.78/1.02      | r2_hidden(sK5(sK6,X0,sK8),sK6) = iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top
% 3.78/1.02      | v1_relat_1(sK8) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_15042,c_11935]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15510,plain,
% 3.78/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) = iProver_top
% 3.78/1.02      | r2_hidden(sK5(sK6,X0,sK8),sK6) = iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top
% 3.78/1.02      | v1_relat_1(sK8) != iProver_top ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_15504,c_15042]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15832,plain,
% 3.78/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) = iProver_top
% 3.78/1.02      | r2_hidden(sK5(sK6,X0,sK8),sK6) = iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_15510,c_14741,c_14954]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_17859,plain,
% 3.78/1.02      ( r2_hidden(sK5(sK6,sK7,sK8),sK6) = iProver_top ),
% 3.78/1.02      inference(forward_subsumption_resolution,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_17854,c_15832]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_1,plain,
% 3.78/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.78/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11964,plain,
% 3.78/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.78/1.02      | v1_xboole_0(X1) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_17861,plain,
% 3.78/1.02      ( v1_xboole_0(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_17859,c_11964]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_18281,plain,
% 3.78/1.02      ( r1_tarski(k1_xboole_0,sK6) != iProver_top
% 3.78/1.02      | r1_tarski(sK8,k1_xboole_0) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_17926,c_128,c_144,c_145,c_148,c_156,c_12306,c_12504,
% 3.78/1.02                 c_16545,c_17861]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_18282,plain,
% 3.78/1.02      ( r1_tarski(sK8,k1_xboole_0) != iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_18281]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_18283,plain,
% 3.78/1.02      ( ~ r1_tarski(sK8,k1_xboole_0) | ~ r1_tarski(k1_xboole_0,sK6) ),
% 3.78/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_18282]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16820,plain,
% 3.78/1.02      ( r1_tarski(sK8,sK8) ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12840,plain,
% 3.78/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK8) | X2 != X0 | sK8 != X1 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_11033]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14374,plain,
% 3.78/1.02      ( ~ r1_tarski(X0,sK8) | r1_tarski(X1,sK8) | X1 != X0 | sK8 != sK8 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_12840]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16819,plain,
% 3.78/1.02      ( r1_tarski(X0,sK8)
% 3.78/1.02      | ~ r1_tarski(sK8,sK8)
% 3.78/1.02      | X0 != sK8
% 3.78/1.02      | sK8 != sK8 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_14374]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16822,plain,
% 3.78/1.02      ( ~ r1_tarski(sK8,sK8)
% 3.78/1.02      | r1_tarski(k1_xboole_0,sK8)
% 3.78/1.02      | sK8 != sK8
% 3.78/1.02      | k1_xboole_0 != sK8 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_16819]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16441,plain,
% 3.78/1.02      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
% 3.78/1.02      | v1_relat_1(X0) != iProver_top
% 3.78/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_16,c_11955]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16504,plain,
% 3.78/1.02      ( v1_relat_1(X0) != iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_16441,c_128,c_144,c_145,c_148,c_12306,c_12504]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16505,plain,
% 3.78/1.02      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top
% 3.78/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_16504]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16512,plain,
% 3.78/1.02      ( r1_tarski(k1_xboole_0,sK6) = iProver_top
% 3.78/1.02      | r1_tarski(k1_xboole_0,sK8) != iProver_top
% 3.78/1.02      | v1_relat_1(sK8) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_15042,c_16505]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_16528,plain,
% 3.78/1.02      ( r1_tarski(k1_xboole_0,sK6)
% 3.78/1.02      | ~ r1_tarski(k1_xboole_0,sK8)
% 3.78/1.02      | ~ v1_relat_1(sK8) ),
% 3.78/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_16512]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11937,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.78/1.02      | v1_funct_1(X0) != iProver_top
% 3.78/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15502,plain,
% 3.78/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_relat_1(sK8)))) = iProver_top
% 3.78/1.02      | v1_funct_1(sK8) != iProver_top
% 3.78/1.02      | v1_relat_1(sK8) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_15042,c_11937]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15699,plain,
% 3.78/1.02      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k2_relat_1(sK8)))) = iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_15502,c_14741,c_14954]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_18,plain,
% 3.78/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ v1_xboole_0(X2)
% 3.78/1.02      | v1_xboole_0(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11953,plain,
% 3.78/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.78/1.02      | v1_xboole_0(X2) != iProver_top
% 3.78/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15705,plain,
% 3.78/1.02      ( v1_xboole_0(k2_relat_1(sK8)) != iProver_top
% 3.78/1.02      | v1_xboole_0(sK8) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_15699,c_11953]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14750,plain,
% 3.78/1.02      ( v1_relat_1(sK8) ),
% 3.78/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_14741]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11030,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12855,plain,
% 3.78/1.02      ( X0 != X1 | sK8 != X1 | sK8 = X0 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_11030]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14135,plain,
% 3.78/1.02      ( X0 != sK8 | sK8 = X0 | sK8 != sK8 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_12855]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_14136,plain,
% 3.78/1.02      ( sK8 != sK8 | sK8 = k1_xboole_0 | k1_xboole_0 != sK8 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_14135]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11029,plain,( X0 = X0 ),theory(equality) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12466,plain,
% 3.78/1.02      ( sK8 = sK8 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_11029]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_3,plain,
% 3.78/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.78/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12442,plain,
% 3.78/1.02      ( ~ v1_xboole_0(sK8) | k1_xboole_0 = sK8 ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_12446,plain,
% 3.78/1.02      ( k1_xboole_0 = sK8 | v1_xboole_0(sK8) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_12442]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_147,plain,
% 3.78/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_49,plain,
% 3.78/1.02      ( r2_hidden(sK8,k1_funct_2(sK6,sK7)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(contradiction,plain,
% 3.78/1.02      ( $false ),
% 3.78/1.02      inference(minisat,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_23076,c_22045,c_18767,c_18283,c_16820,c_16822,c_16528,
% 3.78/1.02                 c_15705,c_14750,c_14136,c_12466,c_12446,c_147,c_145,
% 3.78/1.02                 c_144,c_49]) ).
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/1.02  
% 3.78/1.02  ------                               Statistics
% 3.78/1.02  
% 3.78/1.02  ------ General
% 3.78/1.02  
% 3.78/1.02  abstr_ref_over_cycles:                  0
% 3.78/1.02  abstr_ref_under_cycles:                 0
% 3.78/1.02  gc_basic_clause_elim:                   0
% 3.78/1.02  forced_gc_time:                         0
% 3.78/1.02  parsing_time:                           0.011
% 3.78/1.02  unif_index_cands_time:                  0.
% 3.78/1.02  unif_index_add_time:                    0.
% 3.78/1.02  orderings_time:                         0.
% 3.78/1.02  out_proof_time:                         0.014
% 3.78/1.02  total_time:                             0.413
% 3.78/1.02  num_of_symbols:                         57
% 3.78/1.02  num_of_terms:                           13657
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing
% 3.78/1.02  
% 3.78/1.02  num_of_splits:                          2
% 3.78/1.02  num_of_split_atoms:                     2
% 3.78/1.02  num_of_reused_defs:                     0
% 3.78/1.02  num_eq_ax_congr_red:                    35
% 3.78/1.02  num_of_sem_filtered_clauses:            1
% 3.78/1.02  num_of_subtypes:                        0
% 3.78/1.02  monotx_restored_types:                  0
% 3.78/1.02  sat_num_of_epr_types:                   0
% 3.78/1.02  sat_num_of_non_cyclic_types:            0
% 3.78/1.02  sat_guarded_non_collapsed_types:        0
% 3.78/1.02  num_pure_diseq_elim:                    0
% 3.78/1.02  simp_replaced_by:                       0
% 3.78/1.02  res_preprocessed:                       208
% 3.78/1.02  prep_upred:                             0
% 3.78/1.02  prep_unflattend:                        558
% 3.78/1.02  smt_new_axioms:                         0
% 3.78/1.02  pred_elim_cands:                        7
% 3.78/1.02  pred_elim:                              2
% 3.78/1.02  pred_elim_cl:                           1
% 3.78/1.02  pred_elim_cycles:                       11
% 3.78/1.02  merged_defs:                            8
% 3.78/1.02  merged_defs_ncl:                        0
% 3.78/1.02  bin_hyper_res:                          8
% 3.78/1.02  prep_cycles:                            4
% 3.78/1.02  pred_elim_time:                         0.122
% 3.78/1.02  splitting_time:                         0.
% 3.78/1.02  sem_filter_time:                        0.
% 3.78/1.02  monotx_time:                            0.
% 3.78/1.02  subtype_inf_time:                       0.
% 3.78/1.02  
% 3.78/1.02  ------ Problem properties
% 3.78/1.02  
% 3.78/1.02  clauses:                                44
% 3.78/1.02  conjectures:                            1
% 3.78/1.02  epr:                                    5
% 3.78/1.02  horn:                                   35
% 3.78/1.02  ground:                                 9
% 3.78/1.02  unary:                                  9
% 3.78/1.02  binary:                                 8
% 3.78/1.02  lits:                                   121
% 3.78/1.02  lits_eq:                                21
% 3.78/1.02  fd_pure:                                0
% 3.78/1.02  fd_pseudo:                              0
% 3.78/1.02  fd_cond:                                2
% 3.78/1.02  fd_pseudo_cond:                         2
% 3.78/1.02  ac_symbols:                             0
% 3.78/1.02  
% 3.78/1.02  ------ Propositional Solver
% 3.78/1.02  
% 3.78/1.02  prop_solver_calls:                      30
% 3.78/1.02  prop_fast_solver_calls:                 3827
% 3.78/1.02  smt_solver_calls:                       0
% 3.78/1.02  smt_fast_solver_calls:                  0
% 3.78/1.02  prop_num_of_clauses:                    5301
% 3.78/1.02  prop_preprocess_simplified:             13359
% 3.78/1.02  prop_fo_subsumed:                       70
% 3.78/1.02  prop_solver_time:                       0.
% 3.78/1.02  smt_solver_time:                        0.
% 3.78/1.02  smt_fast_solver_time:                   0.
% 3.78/1.02  prop_fast_solver_time:                  0.
% 3.78/1.02  prop_unsat_core_time:                   0.
% 3.78/1.02  
% 3.78/1.02  ------ QBF
% 3.78/1.02  
% 3.78/1.02  qbf_q_res:                              0
% 3.78/1.02  qbf_num_tautologies:                    0
% 3.78/1.02  qbf_prep_cycles:                        0
% 3.78/1.02  
% 3.78/1.02  ------ BMC1
% 3.78/1.02  
% 3.78/1.02  bmc1_current_bound:                     -1
% 3.78/1.02  bmc1_last_solved_bound:                 -1
% 3.78/1.02  bmc1_unsat_core_size:                   -1
% 3.78/1.02  bmc1_unsat_core_parents_size:           -1
% 3.78/1.02  bmc1_merge_next_fun:                    0
% 3.78/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.78/1.02  
% 3.78/1.02  ------ Instantiation
% 3.78/1.02  
% 3.78/1.02  inst_num_of_clauses:                    1273
% 3.78/1.02  inst_num_in_passive:                    513
% 3.78/1.02  inst_num_in_active:                     548
% 3.78/1.02  inst_num_in_unprocessed:                212
% 3.78/1.02  inst_num_of_loops:                      736
% 3.78/1.02  inst_num_of_learning_restarts:          0
% 3.78/1.02  inst_num_moves_active_passive:          183
% 3.78/1.02  inst_lit_activity:                      0
% 3.78/1.02  inst_lit_activity_moves:                0
% 3.78/1.02  inst_num_tautologies:                   0
% 3.78/1.02  inst_num_prop_implied:                  0
% 3.78/1.02  inst_num_existing_simplified:           0
% 3.78/1.02  inst_num_eq_res_simplified:             0
% 3.78/1.02  inst_num_child_elim:                    0
% 3.78/1.02  inst_num_of_dismatching_blockings:      690
% 3.78/1.02  inst_num_of_non_proper_insts:           1419
% 3.78/1.02  inst_num_of_duplicates:                 0
% 3.78/1.02  inst_inst_num_from_inst_to_res:         0
% 3.78/1.02  inst_dismatching_checking_time:         0.
% 3.78/1.02  
% 3.78/1.02  ------ Resolution
% 3.78/1.02  
% 3.78/1.02  res_num_of_clauses:                     0
% 3.78/1.02  res_num_in_passive:                     0
% 3.78/1.02  res_num_in_active:                      0
% 3.78/1.02  res_num_of_loops:                       212
% 3.78/1.02  res_forward_subset_subsumed:            42
% 3.78/1.02  res_backward_subset_subsumed:           2
% 3.78/1.02  res_forward_subsumed:                   2
% 3.78/1.02  res_backward_subsumed:                  1
% 3.78/1.02  res_forward_subsumption_resolution:     9
% 3.78/1.02  res_backward_subsumption_resolution:    0
% 3.78/1.02  res_clause_to_clause_subsumption:       1445
% 3.78/1.02  res_orphan_elimination:                 0
% 3.78/1.02  res_tautology_del:                      84
% 3.78/1.02  res_num_eq_res_simplified:              0
% 3.78/1.02  res_num_sel_changes:                    0
% 3.78/1.02  res_moves_from_active_to_pass:          0
% 3.78/1.02  
% 3.78/1.02  ------ Superposition
% 3.78/1.02  
% 3.78/1.02  sup_time_total:                         0.
% 3.78/1.02  sup_time_generating:                    0.
% 3.78/1.02  sup_time_sim_full:                      0.
% 3.78/1.02  sup_time_sim_immed:                     0.
% 3.78/1.02  
% 3.78/1.02  sup_num_of_clauses:                     253
% 3.78/1.02  sup_num_in_active:                      136
% 3.78/1.02  sup_num_in_passive:                     117
% 3.78/1.02  sup_num_of_loops:                       146
% 3.78/1.02  sup_fw_superposition:                   142
% 3.78/1.02  sup_bw_superposition:                   159
% 3.78/1.02  sup_immediate_simplified:               66
% 3.78/1.02  sup_given_eliminated:                   2
% 3.78/1.02  comparisons_done:                       0
% 3.78/1.02  comparisons_avoided:                    6
% 3.78/1.02  
% 3.78/1.02  ------ Simplifications
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  sim_fw_subset_subsumed:                 24
% 3.78/1.02  sim_bw_subset_subsumed:                 5
% 3.78/1.02  sim_fw_subsumed:                        19
% 3.78/1.02  sim_bw_subsumed:                        7
% 3.78/1.02  sim_fw_subsumption_res:                 5
% 3.78/1.02  sim_bw_subsumption_res:                 0
% 3.78/1.02  sim_tautology_del:                      12
% 3.78/1.02  sim_eq_tautology_del:                   5
% 3.78/1.02  sim_eq_res_simp:                        5
% 3.78/1.02  sim_fw_demodulated:                     7
% 3.78/1.02  sim_bw_demodulated:                     8
% 3.78/1.02  sim_light_normalised:                   31
% 3.78/1.02  sim_joinable_taut:                      0
% 3.78/1.02  sim_joinable_simp:                      0
% 3.78/1.02  sim_ac_normalised:                      0
% 3.78/1.02  sim_smt_subsumption:                    0
% 3.78/1.02  
%------------------------------------------------------------------------------

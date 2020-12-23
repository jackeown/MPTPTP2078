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

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  220 (1832 expanded)
%              Number of clauses        :  137 ( 649 expanded)
%              Number of leaves         :   27 ( 459 expanded)
%              Depth                    :   25
%              Number of atoms          :  802 (10973 expanded)
%              Number of equality atoms :  303 (3340 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,
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

fof(f59,plain,
    ( ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      | ~ v1_funct_2(sK9,sK7,sK8)
      | ~ v1_funct_1(sK9) )
    & r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f35,f58])).

fof(f103,plain,(
    r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(cnf_transformation,[],[f59])).

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
    inference(definition_folding,[],[f13,f36])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f110,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f50,f53,f52,f51])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( sK5(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK5(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
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

fof(f79,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f95,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f18])).

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
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f56])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f114,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f99])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_44,negated_conjecture,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6652,plain,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_33,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_6656,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK5(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6660,plain,
    ( sK5(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_9281,plain,
    ( sK5(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6656,c_6660])).

cnf(c_9406,plain,
    ( sK5(sK8,sK7,sK9) = sK9 ),
    inference(superposition,[status(thm)],[c_6652,c_9281])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6662,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9953,plain,
    ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6656,c_6662])).

cnf(c_20176,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9406,c_9953])).

cnf(c_45,plain,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_20470,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20176,c_45])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6670,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK5(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_6661,plain,
    ( k1_relat_1(sK5(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9399,plain,
    ( k1_relat_1(sK5(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6656,c_6661])).

cnf(c_11042,plain,
    ( k1_relat_1(sK5(sK8,sK7,sK9)) = sK7 ),
    inference(superposition,[status(thm)],[c_6652,c_9399])).

cnf(c_11053,plain,
    ( k1_relat_1(sK9) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_11042,c_9406])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_567,plain,
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

cnf(c_568,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_572,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_34])).

cnf(c_16,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_43,negated_conjecture,
    ( ~ v1_funct_2(sK9,sK7,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_647,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | sK8 != X2
    | sK7 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_43])).

cnf(c_648,plain,
    ( ~ v1_partfun1(sK9,sK7)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_800,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK7
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_572,c_648])).

cnf(c_801,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | v1_xboole_0(k2_relat_1(sK9))
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_6644,plain,
    ( k1_relat_1(sK9) != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_11206,plain,
    ( sK7 != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11053,c_6644])).

cnf(c_11252,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11206])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_139,plain,
    ( r1_tarski(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_143,plain,
    ( ~ r1_tarski(sK9,sK9)
    | sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_802,plain,
    ( k1_relat_1(sK9) != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK5(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7051,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_funct_1(sK5(X0,X1,sK9)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_7207,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_funct_1(sK5(sK8,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_7051])).

cnf(c_7209,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
    | v1_funct_1(sK5(sK8,sK7,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7207])).

cnf(c_7208,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_7211,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7208])).

cnf(c_5743,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7399,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK5(sK8,sK7,sK9))
    | X0 != sK5(sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_5743])).

cnf(c_7400,plain,
    ( X0 != sK5(sK8,sK7,sK9)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK5(sK8,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7399])).

cnf(c_7402,plain,
    ( sK9 != sK5(sK8,sK7,sK9)
    | v1_funct_1(sK5(sK8,sK7,sK9)) != iProver_top
    | v1_funct_1(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7400])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK5(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7056,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_relat_1(sK5(X0,X1,sK9)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_7432,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_relat_1(sK5(sK8,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_7056])).

cnf(c_7434,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
    | v1_relat_1(sK5(sK8,sK7,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7432])).

cnf(c_7093,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | sK5(X0,X1,sK9) = sK9 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_7431,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | sK5(sK8,sK7,sK9) = sK9 ),
    inference(instantiation,[status(thm)],[c_7093])).

cnf(c_5733,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7698,plain,
    ( X0 != X1
    | X0 = sK5(sK8,sK7,sK9)
    | sK5(sK8,sK7,sK9) != X1 ),
    inference(instantiation,[status(thm)],[c_5733])).

cnf(c_7699,plain,
    ( sK5(sK8,sK7,sK9) != sK9
    | sK9 = sK5(sK8,sK7,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_7698])).

cnf(c_5742,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7993,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK5(sK8,sK7,sK9))
    | X0 != sK5(sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_5742])).

cnf(c_7999,plain,
    ( X0 != sK5(sK8,sK7,sK9)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7993])).

cnf(c_8001,plain,
    ( sK9 != sK5(sK8,sK7,sK9)
    | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7999])).

cnf(c_17497,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11252,c_44,c_45,c_139,c_143,c_802,c_7209,c_7208,c_7211,c_7402,c_7434,c_7431,c_7699,c_8001,c_11053])).

cnf(c_17504,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(k1_relat_1(sK9),sK7) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6670,c_17497])).

cnf(c_17511,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17504,c_11053])).

cnf(c_17825,plain,
    ( r1_tarski(sK7,sK7) != iProver_top
    | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17511,c_44,c_45,c_139,c_143,c_7208,c_7211,c_7434,c_7431,c_7699,c_8001])).

cnf(c_17826,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(renaming,[status(thm)],[c_17825])).

cnf(c_6677,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17832,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17826,c_6677])).

cnf(c_20481,plain,
    ( v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20470,c_17832])).

cnf(c_6655,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11364,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_11053,c_6655])).

cnf(c_11471,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11364,c_44,c_45,c_139,c_143,c_7209,c_7208,c_7211,c_7402,c_7434,c_7431,c_7699,c_8001])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6673,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11478,plain,
    ( v1_xboole_0(k2_relat_1(sK9)) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_11471,c_6673])).

cnf(c_21086,plain,
    ( v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_20481,c_11478])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6680,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6682,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7829,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6680,c_6682])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6675,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6671,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7977,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6675,c_6671])).

cnf(c_8165,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7829,c_7977])).

cnf(c_24489,plain,
    ( k1_relset_1(X0,X1,sK9) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_21086,c_8165])).

cnf(c_24491,plain,
    ( k1_relset_1(X0,X1,sK9) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_24489,c_11053])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6674,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8504,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6672,c_6674])).

cnf(c_9053,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6675,c_8504])).

cnf(c_24509,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24491,c_9053])).

cnf(c_24542,plain,
    ( r1_tarski(sK7,sK9) = iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(sK9,sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24509])).

cnf(c_8628,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6675,c_6673])).

cnf(c_20259,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6677,c_8628])).

cnf(c_6678,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8057,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7829,c_6678])).

cnf(c_8270,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7829,c_8057])).

cnf(c_21715,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_20259,c_8270])).

cnf(c_21733,plain,
    ( k2_zfmisc_1(sK9,sK9) = sK9
    | v1_xboole_0(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_21715])).

cnf(c_14731,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_5733])).

cnf(c_14732,plain,
    ( k2_zfmisc_1(sK9,sK9) != sK9
    | sK9 = k2_zfmisc_1(sK9,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_14731])).

cnf(c_40,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_679,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK7
    | sK8 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_43])).

cnf(c_680,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_6649,plain,
    ( k1_relat_1(sK9) != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9)) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_11210,plain,
    ( sK7 != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11053,c_6649])).

cnf(c_11221,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11210])).

cnf(c_12582,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11221,c_44,c_45,c_139,c_143,c_7209,c_7208,c_7211,c_7402,c_7434,c_7431,c_7699,c_8001])).

cnf(c_12589,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(k1_relat_1(sK9),sK7) != iProver_top
    | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6670,c_12582])).

cnf(c_12594,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top
    | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12589,c_11053])).

cnf(c_12842,plain,
    ( r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
    | r1_tarski(sK7,sK7) != iProver_top
    | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12594,c_44,c_45,c_139,c_143,c_7208,c_7211,c_7434,c_7431,c_7699,c_8001])).

cnf(c_12843,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top
    | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_12842])).

cnf(c_12849,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12843,c_6677])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_334,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_335,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_403,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_335])).

cnf(c_6651,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_12853,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(sK7,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12849,c_6651])).

cnf(c_12875,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(sK7,sK9) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12853])).

cnf(c_5736,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_7297,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(X3,k2_zfmisc_1(X1,X2))
    | X3 != X0 ),
    inference(instantiation,[status(thm)],[c_5736])).

cnf(c_10318,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_7297])).

cnf(c_10319,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10318])).

cnf(c_10321,plain,
    ( sK9 != k2_zfmisc_1(sK9,sK9)
    | r1_tarski(k2_zfmisc_1(sK9,sK9),k2_zfmisc_1(sK9,sK9)) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(sK9,sK9)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10319])).

cnf(c_7288,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7293,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7288])).

cnf(c_7295,plain,
    ( r1_tarski(k2_zfmisc_1(sK9,sK9),k2_zfmisc_1(sK9,sK9)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7293])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24542,c_21733,c_20176,c_17832,c_14732,c_12875,c_11478,c_10321,c_7295,c_143,c_139,c_45])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.93/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/1.00  
% 3.93/1.00  ------  iProver source info
% 3.93/1.00  
% 3.93/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.93/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/1.00  git: non_committed_changes: false
% 3.93/1.00  git: last_make_outside_of_git: false
% 3.93/1.00  
% 3.93/1.00  ------ 
% 3.93/1.00  
% 3.93/1.00  ------ Input Options
% 3.93/1.00  
% 3.93/1.00  --out_options                           all
% 3.93/1.00  --tptp_safe_out                         true
% 3.93/1.00  --problem_path                          ""
% 3.93/1.00  --include_path                          ""
% 3.93/1.00  --clausifier                            res/vclausify_rel
% 3.93/1.00  --clausifier_options                    --mode clausify
% 3.93/1.00  --stdin                                 false
% 3.93/1.00  --stats_out                             all
% 3.93/1.00  
% 3.93/1.00  ------ General Options
% 3.93/1.00  
% 3.93/1.00  --fof                                   false
% 3.93/1.00  --time_out_real                         305.
% 3.93/1.00  --time_out_virtual                      -1.
% 3.93/1.00  --symbol_type_check                     false
% 3.93/1.00  --clausify_out                          false
% 3.93/1.00  --sig_cnt_out                           false
% 3.93/1.00  --trig_cnt_out                          false
% 3.93/1.00  --trig_cnt_out_tolerance                1.
% 3.93/1.00  --trig_cnt_out_sk_spl                   false
% 3.93/1.00  --abstr_cl_out                          false
% 3.93/1.00  
% 3.93/1.00  ------ Global Options
% 3.93/1.00  
% 3.93/1.00  --schedule                              default
% 3.93/1.00  --add_important_lit                     false
% 3.93/1.00  --prop_solver_per_cl                    1000
% 3.93/1.00  --min_unsat_core                        false
% 3.93/1.00  --soft_assumptions                      false
% 3.93/1.00  --soft_lemma_size                       3
% 3.93/1.00  --prop_impl_unit_size                   0
% 3.93/1.00  --prop_impl_unit                        []
% 3.93/1.00  --share_sel_clauses                     true
% 3.93/1.00  --reset_solvers                         false
% 3.93/1.00  --bc_imp_inh                            [conj_cone]
% 3.93/1.00  --conj_cone_tolerance                   3.
% 3.93/1.00  --extra_neg_conj                        none
% 3.93/1.00  --large_theory_mode                     true
% 3.93/1.00  --prolific_symb_bound                   200
% 3.93/1.00  --lt_threshold                          2000
% 3.93/1.00  --clause_weak_htbl                      true
% 3.93/1.00  --gc_record_bc_elim                     false
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing Options
% 3.93/1.00  
% 3.93/1.00  --preprocessing_flag                    true
% 3.93/1.00  --time_out_prep_mult                    0.1
% 3.93/1.00  --splitting_mode                        input
% 3.93/1.00  --splitting_grd                         true
% 3.93/1.00  --splitting_cvd                         false
% 3.93/1.00  --splitting_cvd_svl                     false
% 3.93/1.00  --splitting_nvd                         32
% 3.93/1.00  --sub_typing                            true
% 3.93/1.00  --prep_gs_sim                           true
% 3.93/1.00  --prep_unflatten                        true
% 3.93/1.00  --prep_res_sim                          true
% 3.93/1.00  --prep_upred                            true
% 3.93/1.00  --prep_sem_filter                       exhaustive
% 3.93/1.00  --prep_sem_filter_out                   false
% 3.93/1.00  --pred_elim                             true
% 3.93/1.00  --res_sim_input                         true
% 3.93/1.00  --eq_ax_congr_red                       true
% 3.93/1.00  --pure_diseq_elim                       true
% 3.93/1.00  --brand_transform                       false
% 3.93/1.00  --non_eq_to_eq                          false
% 3.93/1.00  --prep_def_merge                        true
% 3.93/1.00  --prep_def_merge_prop_impl              false
% 3.93/1.00  --prep_def_merge_mbd                    true
% 3.93/1.00  --prep_def_merge_tr_red                 false
% 3.93/1.00  --prep_def_merge_tr_cl                  false
% 3.93/1.00  --smt_preprocessing                     true
% 3.93/1.00  --smt_ac_axioms                         fast
% 3.93/1.00  --preprocessed_out                      false
% 3.93/1.00  --preprocessed_stats                    false
% 3.93/1.00  
% 3.93/1.00  ------ Abstraction refinement Options
% 3.93/1.00  
% 3.93/1.00  --abstr_ref                             []
% 3.93/1.00  --abstr_ref_prep                        false
% 3.93/1.00  --abstr_ref_until_sat                   false
% 3.93/1.00  --abstr_ref_sig_restrict                funpre
% 3.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/1.00  --abstr_ref_under                       []
% 3.93/1.00  
% 3.93/1.00  ------ SAT Options
% 3.93/1.00  
% 3.93/1.00  --sat_mode                              false
% 3.93/1.00  --sat_fm_restart_options                ""
% 3.93/1.00  --sat_gr_def                            false
% 3.93/1.00  --sat_epr_types                         true
% 3.93/1.00  --sat_non_cyclic_types                  false
% 3.93/1.00  --sat_finite_models                     false
% 3.93/1.00  --sat_fm_lemmas                         false
% 3.93/1.00  --sat_fm_prep                           false
% 3.93/1.00  --sat_fm_uc_incr                        true
% 3.93/1.00  --sat_out_model                         small
% 3.93/1.00  --sat_out_clauses                       false
% 3.93/1.00  
% 3.93/1.00  ------ QBF Options
% 3.93/1.00  
% 3.93/1.00  --qbf_mode                              false
% 3.93/1.00  --qbf_elim_univ                         false
% 3.93/1.00  --qbf_dom_inst                          none
% 3.93/1.00  --qbf_dom_pre_inst                      false
% 3.93/1.00  --qbf_sk_in                             false
% 3.93/1.00  --qbf_pred_elim                         true
% 3.93/1.00  --qbf_split                             512
% 3.93/1.00  
% 3.93/1.00  ------ BMC1 Options
% 3.93/1.00  
% 3.93/1.00  --bmc1_incremental                      false
% 3.93/1.00  --bmc1_axioms                           reachable_all
% 3.93/1.00  --bmc1_min_bound                        0
% 3.93/1.00  --bmc1_max_bound                        -1
% 3.93/1.00  --bmc1_max_bound_default                -1
% 3.93/1.00  --bmc1_symbol_reachability              true
% 3.93/1.00  --bmc1_property_lemmas                  false
% 3.93/1.00  --bmc1_k_induction                      false
% 3.93/1.00  --bmc1_non_equiv_states                 false
% 3.93/1.00  --bmc1_deadlock                         false
% 3.93/1.00  --bmc1_ucm                              false
% 3.93/1.00  --bmc1_add_unsat_core                   none
% 3.93/1.00  --bmc1_unsat_core_children              false
% 3.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/1.00  --bmc1_out_stat                         full
% 3.93/1.00  --bmc1_ground_init                      false
% 3.93/1.00  --bmc1_pre_inst_next_state              false
% 3.93/1.00  --bmc1_pre_inst_state                   false
% 3.93/1.00  --bmc1_pre_inst_reach_state             false
% 3.93/1.00  --bmc1_out_unsat_core                   false
% 3.93/1.00  --bmc1_aig_witness_out                  false
% 3.93/1.00  --bmc1_verbose                          false
% 3.93/1.00  --bmc1_dump_clauses_tptp                false
% 3.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.93/1.00  --bmc1_dump_file                        -
% 3.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.93/1.00  --bmc1_ucm_extend_mode                  1
% 3.93/1.00  --bmc1_ucm_init_mode                    2
% 3.93/1.00  --bmc1_ucm_cone_mode                    none
% 3.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.93/1.00  --bmc1_ucm_relax_model                  4
% 3.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/1.00  --bmc1_ucm_layered_model                none
% 3.93/1.00  --bmc1_ucm_max_lemma_size               10
% 3.93/1.00  
% 3.93/1.00  ------ AIG Options
% 3.93/1.00  
% 3.93/1.00  --aig_mode                              false
% 3.93/1.00  
% 3.93/1.00  ------ Instantiation Options
% 3.93/1.00  
% 3.93/1.00  --instantiation_flag                    true
% 3.93/1.00  --inst_sos_flag                         false
% 3.93/1.00  --inst_sos_phase                        true
% 3.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel_side                     num_symb
% 3.93/1.00  --inst_solver_per_active                1400
% 3.93/1.00  --inst_solver_calls_frac                1.
% 3.93/1.00  --inst_passive_queue_type               priority_queues
% 3.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/1.00  --inst_passive_queues_freq              [25;2]
% 3.93/1.00  --inst_dismatching                      true
% 3.93/1.00  --inst_eager_unprocessed_to_passive     true
% 3.93/1.00  --inst_prop_sim_given                   true
% 3.93/1.00  --inst_prop_sim_new                     false
% 3.93/1.00  --inst_subs_new                         false
% 3.93/1.00  --inst_eq_res_simp                      false
% 3.93/1.00  --inst_subs_given                       false
% 3.93/1.00  --inst_orphan_elimination               true
% 3.93/1.00  --inst_learning_loop_flag               true
% 3.93/1.00  --inst_learning_start                   3000
% 3.93/1.00  --inst_learning_factor                  2
% 3.93/1.00  --inst_start_prop_sim_after_learn       3
% 3.93/1.00  --inst_sel_renew                        solver
% 3.93/1.00  --inst_lit_activity_flag                true
% 3.93/1.00  --inst_restr_to_given                   false
% 3.93/1.00  --inst_activity_threshold               500
% 3.93/1.00  --inst_out_proof                        true
% 3.93/1.00  
% 3.93/1.00  ------ Resolution Options
% 3.93/1.00  
% 3.93/1.00  --resolution_flag                       true
% 3.93/1.00  --res_lit_sel                           adaptive
% 3.93/1.00  --res_lit_sel_side                      none
% 3.93/1.00  --res_ordering                          kbo
% 3.93/1.00  --res_to_prop_solver                    active
% 3.93/1.00  --res_prop_simpl_new                    false
% 3.93/1.00  --res_prop_simpl_given                  true
% 3.93/1.00  --res_passive_queue_type                priority_queues
% 3.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/1.00  --res_passive_queues_freq               [15;5]
% 3.93/1.00  --res_forward_subs                      full
% 3.93/1.00  --res_backward_subs                     full
% 3.93/1.00  --res_forward_subs_resolution           true
% 3.93/1.00  --res_backward_subs_resolution          true
% 3.93/1.00  --res_orphan_elimination                true
% 3.93/1.00  --res_time_limit                        2.
% 3.93/1.00  --res_out_proof                         true
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Options
% 3.93/1.00  
% 3.93/1.00  --superposition_flag                    true
% 3.93/1.00  --sup_passive_queue_type                priority_queues
% 3.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.93/1.00  --demod_completeness_check              fast
% 3.93/1.00  --demod_use_ground                      true
% 3.93/1.00  --sup_to_prop_solver                    passive
% 3.93/1.00  --sup_prop_simpl_new                    true
% 3.93/1.00  --sup_prop_simpl_given                  true
% 3.93/1.00  --sup_fun_splitting                     false
% 3.93/1.00  --sup_smt_interval                      50000
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Simplification Setup
% 3.93/1.00  
% 3.93/1.00  --sup_indices_passive                   []
% 3.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_full_bw                           [BwDemod]
% 3.93/1.00  --sup_immed_triv                        [TrivRules]
% 3.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_immed_bw_main                     []
% 3.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/1.00  
% 3.93/1.00  ------ Combination Options
% 3.93/1.00  
% 3.93/1.00  --comb_res_mult                         3
% 3.93/1.00  --comb_sup_mult                         2
% 3.93/1.00  --comb_inst_mult                        10
% 3.93/1.00  
% 3.93/1.00  ------ Debug Options
% 3.93/1.00  
% 3.93/1.00  --dbg_backtrace                         false
% 3.93/1.00  --dbg_dump_prop_clauses                 false
% 3.93/1.00  --dbg_dump_prop_clauses_file            -
% 3.93/1.00  --dbg_out_stat                          false
% 3.93/1.00  ------ Parsing...
% 3.93/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/1.00  ------ Proving...
% 3.93/1.00  ------ Problem Properties 
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  clauses                                 40
% 3.93/1.00  conjectures                             1
% 3.93/1.00  EPR                                     6
% 3.93/1.00  Horn                                    31
% 3.93/1.00  unary                                   3
% 3.93/1.00  binary                                  10
% 3.93/1.00  lits                                    122
% 3.93/1.00  lits eq                                 14
% 3.93/1.00  fd_pure                                 0
% 3.93/1.00  fd_pseudo                               0
% 3.93/1.00  fd_cond                                 0
% 3.93/1.00  fd_pseudo_cond                          2
% 3.93/1.00  AC symbols                              0
% 3.93/1.00  
% 3.93/1.00  ------ Schedule dynamic 5 is on 
% 3.93/1.00  
% 3.93/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ 
% 3.93/1.00  Current options:
% 3.93/1.00  ------ 
% 3.93/1.00  
% 3.93/1.00  ------ Input Options
% 3.93/1.00  
% 3.93/1.00  --out_options                           all
% 3.93/1.00  --tptp_safe_out                         true
% 3.93/1.00  --problem_path                          ""
% 3.93/1.00  --include_path                          ""
% 3.93/1.00  --clausifier                            res/vclausify_rel
% 3.93/1.00  --clausifier_options                    --mode clausify
% 3.93/1.00  --stdin                                 false
% 3.93/1.00  --stats_out                             all
% 3.93/1.00  
% 3.93/1.00  ------ General Options
% 3.93/1.00  
% 3.93/1.00  --fof                                   false
% 3.93/1.00  --time_out_real                         305.
% 3.93/1.00  --time_out_virtual                      -1.
% 3.93/1.00  --symbol_type_check                     false
% 3.93/1.00  --clausify_out                          false
% 3.93/1.00  --sig_cnt_out                           false
% 3.93/1.00  --trig_cnt_out                          false
% 3.93/1.00  --trig_cnt_out_tolerance                1.
% 3.93/1.00  --trig_cnt_out_sk_spl                   false
% 3.93/1.00  --abstr_cl_out                          false
% 3.93/1.00  
% 3.93/1.00  ------ Global Options
% 3.93/1.00  
% 3.93/1.00  --schedule                              default
% 3.93/1.00  --add_important_lit                     false
% 3.93/1.00  --prop_solver_per_cl                    1000
% 3.93/1.00  --min_unsat_core                        false
% 3.93/1.00  --soft_assumptions                      false
% 3.93/1.00  --soft_lemma_size                       3
% 3.93/1.00  --prop_impl_unit_size                   0
% 3.93/1.00  --prop_impl_unit                        []
% 3.93/1.00  --share_sel_clauses                     true
% 3.93/1.00  --reset_solvers                         false
% 3.93/1.00  --bc_imp_inh                            [conj_cone]
% 3.93/1.00  --conj_cone_tolerance                   3.
% 3.93/1.00  --extra_neg_conj                        none
% 3.93/1.00  --large_theory_mode                     true
% 3.93/1.00  --prolific_symb_bound                   200
% 3.93/1.00  --lt_threshold                          2000
% 3.93/1.00  --clause_weak_htbl                      true
% 3.93/1.00  --gc_record_bc_elim                     false
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing Options
% 3.93/1.00  
% 3.93/1.00  --preprocessing_flag                    true
% 3.93/1.00  --time_out_prep_mult                    0.1
% 3.93/1.00  --splitting_mode                        input
% 3.93/1.00  --splitting_grd                         true
% 3.93/1.00  --splitting_cvd                         false
% 3.93/1.00  --splitting_cvd_svl                     false
% 3.93/1.00  --splitting_nvd                         32
% 3.93/1.00  --sub_typing                            true
% 3.93/1.00  --prep_gs_sim                           true
% 3.93/1.00  --prep_unflatten                        true
% 3.93/1.00  --prep_res_sim                          true
% 3.93/1.00  --prep_upred                            true
% 3.93/1.00  --prep_sem_filter                       exhaustive
% 3.93/1.00  --prep_sem_filter_out                   false
% 3.93/1.00  --pred_elim                             true
% 3.93/1.00  --res_sim_input                         true
% 3.93/1.00  --eq_ax_congr_red                       true
% 3.93/1.00  --pure_diseq_elim                       true
% 3.93/1.00  --brand_transform                       false
% 3.93/1.00  --non_eq_to_eq                          false
% 3.93/1.00  --prep_def_merge                        true
% 3.93/1.00  --prep_def_merge_prop_impl              false
% 3.93/1.00  --prep_def_merge_mbd                    true
% 3.93/1.00  --prep_def_merge_tr_red                 false
% 3.93/1.00  --prep_def_merge_tr_cl                  false
% 3.93/1.00  --smt_preprocessing                     true
% 3.93/1.00  --smt_ac_axioms                         fast
% 3.93/1.00  --preprocessed_out                      false
% 3.93/1.00  --preprocessed_stats                    false
% 3.93/1.00  
% 3.93/1.00  ------ Abstraction refinement Options
% 3.93/1.00  
% 3.93/1.00  --abstr_ref                             []
% 3.93/1.00  --abstr_ref_prep                        false
% 3.93/1.00  --abstr_ref_until_sat                   false
% 3.93/1.00  --abstr_ref_sig_restrict                funpre
% 3.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/1.00  --abstr_ref_under                       []
% 3.93/1.00  
% 3.93/1.00  ------ SAT Options
% 3.93/1.00  
% 3.93/1.00  --sat_mode                              false
% 3.93/1.00  --sat_fm_restart_options                ""
% 3.93/1.00  --sat_gr_def                            false
% 3.93/1.00  --sat_epr_types                         true
% 3.93/1.00  --sat_non_cyclic_types                  false
% 3.93/1.00  --sat_finite_models                     false
% 3.93/1.00  --sat_fm_lemmas                         false
% 3.93/1.00  --sat_fm_prep                           false
% 3.93/1.00  --sat_fm_uc_incr                        true
% 3.93/1.00  --sat_out_model                         small
% 3.93/1.00  --sat_out_clauses                       false
% 3.93/1.00  
% 3.93/1.00  ------ QBF Options
% 3.93/1.00  
% 3.93/1.00  --qbf_mode                              false
% 3.93/1.00  --qbf_elim_univ                         false
% 3.93/1.00  --qbf_dom_inst                          none
% 3.93/1.00  --qbf_dom_pre_inst                      false
% 3.93/1.00  --qbf_sk_in                             false
% 3.93/1.00  --qbf_pred_elim                         true
% 3.93/1.00  --qbf_split                             512
% 3.93/1.00  
% 3.93/1.00  ------ BMC1 Options
% 3.93/1.00  
% 3.93/1.00  --bmc1_incremental                      false
% 3.93/1.00  --bmc1_axioms                           reachable_all
% 3.93/1.00  --bmc1_min_bound                        0
% 3.93/1.00  --bmc1_max_bound                        -1
% 3.93/1.00  --bmc1_max_bound_default                -1
% 3.93/1.00  --bmc1_symbol_reachability              true
% 3.93/1.00  --bmc1_property_lemmas                  false
% 3.93/1.00  --bmc1_k_induction                      false
% 3.93/1.00  --bmc1_non_equiv_states                 false
% 3.93/1.00  --bmc1_deadlock                         false
% 3.93/1.00  --bmc1_ucm                              false
% 3.93/1.00  --bmc1_add_unsat_core                   none
% 3.93/1.00  --bmc1_unsat_core_children              false
% 3.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/1.00  --bmc1_out_stat                         full
% 3.93/1.00  --bmc1_ground_init                      false
% 3.93/1.00  --bmc1_pre_inst_next_state              false
% 3.93/1.00  --bmc1_pre_inst_state                   false
% 3.93/1.00  --bmc1_pre_inst_reach_state             false
% 3.93/1.00  --bmc1_out_unsat_core                   false
% 3.93/1.00  --bmc1_aig_witness_out                  false
% 3.93/1.00  --bmc1_verbose                          false
% 3.93/1.00  --bmc1_dump_clauses_tptp                false
% 3.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.93/1.00  --bmc1_dump_file                        -
% 3.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.93/1.00  --bmc1_ucm_extend_mode                  1
% 3.93/1.00  --bmc1_ucm_init_mode                    2
% 3.93/1.00  --bmc1_ucm_cone_mode                    none
% 3.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.93/1.00  --bmc1_ucm_relax_model                  4
% 3.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/1.00  --bmc1_ucm_layered_model                none
% 3.93/1.00  --bmc1_ucm_max_lemma_size               10
% 3.93/1.00  
% 3.93/1.00  ------ AIG Options
% 3.93/1.00  
% 3.93/1.00  --aig_mode                              false
% 3.93/1.00  
% 3.93/1.00  ------ Instantiation Options
% 3.93/1.00  
% 3.93/1.00  --instantiation_flag                    true
% 3.93/1.00  --inst_sos_flag                         false
% 3.93/1.00  --inst_sos_phase                        true
% 3.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel_side                     none
% 3.93/1.00  --inst_solver_per_active                1400
% 3.93/1.00  --inst_solver_calls_frac                1.
% 3.93/1.00  --inst_passive_queue_type               priority_queues
% 3.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/1.00  --inst_passive_queues_freq              [25;2]
% 3.93/1.00  --inst_dismatching                      true
% 3.93/1.00  --inst_eager_unprocessed_to_passive     true
% 3.93/1.00  --inst_prop_sim_given                   true
% 3.93/1.00  --inst_prop_sim_new                     false
% 3.93/1.00  --inst_subs_new                         false
% 3.93/1.00  --inst_eq_res_simp                      false
% 3.93/1.00  --inst_subs_given                       false
% 3.93/1.00  --inst_orphan_elimination               true
% 3.93/1.00  --inst_learning_loop_flag               true
% 3.93/1.00  --inst_learning_start                   3000
% 3.93/1.00  --inst_learning_factor                  2
% 3.93/1.00  --inst_start_prop_sim_after_learn       3
% 3.93/1.00  --inst_sel_renew                        solver
% 3.93/1.00  --inst_lit_activity_flag                true
% 3.93/1.00  --inst_restr_to_given                   false
% 3.93/1.00  --inst_activity_threshold               500
% 3.93/1.00  --inst_out_proof                        true
% 3.93/1.00  
% 3.93/1.00  ------ Resolution Options
% 3.93/1.00  
% 3.93/1.00  --resolution_flag                       false
% 3.93/1.00  --res_lit_sel                           adaptive
% 3.93/1.00  --res_lit_sel_side                      none
% 3.93/1.00  --res_ordering                          kbo
% 3.93/1.00  --res_to_prop_solver                    active
% 3.93/1.00  --res_prop_simpl_new                    false
% 3.93/1.00  --res_prop_simpl_given                  true
% 3.93/1.00  --res_passive_queue_type                priority_queues
% 3.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/1.00  --res_passive_queues_freq               [15;5]
% 3.93/1.00  --res_forward_subs                      full
% 3.93/1.00  --res_backward_subs                     full
% 3.93/1.00  --res_forward_subs_resolution           true
% 3.93/1.00  --res_backward_subs_resolution          true
% 3.93/1.00  --res_orphan_elimination                true
% 3.93/1.00  --res_time_limit                        2.
% 3.93/1.00  --res_out_proof                         true
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Options
% 3.93/1.00  
% 3.93/1.00  --superposition_flag                    true
% 3.93/1.00  --sup_passive_queue_type                priority_queues
% 3.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.93/1.00  --demod_completeness_check              fast
% 3.93/1.00  --demod_use_ground                      true
% 3.93/1.00  --sup_to_prop_solver                    passive
% 3.93/1.00  --sup_prop_simpl_new                    true
% 3.93/1.00  --sup_prop_simpl_given                  true
% 3.93/1.00  --sup_fun_splitting                     false
% 3.93/1.00  --sup_smt_interval                      50000
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Simplification Setup
% 3.93/1.00  
% 3.93/1.00  --sup_indices_passive                   []
% 3.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_full_bw                           [BwDemod]
% 3.93/1.00  --sup_immed_triv                        [TrivRules]
% 3.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_immed_bw_main                     []
% 3.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/1.00  
% 3.93/1.00  ------ Combination Options
% 3.93/1.00  
% 3.93/1.00  --comb_res_mult                         3
% 3.93/1.00  --comb_sup_mult                         2
% 3.93/1.00  --comb_inst_mult                        10
% 3.93/1.00  
% 3.93/1.00  ------ Debug Options
% 3.93/1.00  
% 3.93/1.00  --dbg_backtrace                         false
% 3.93/1.00  --dbg_dump_prop_clauses                 false
% 3.93/1.00  --dbg_dump_prop_clauses_file            -
% 3.93/1.00  --dbg_out_stat                          false
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ Proving...
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  % SZS status Theorem for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  fof(f16,conjecture,(
% 3.93/1.00    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f17,negated_conjecture,(
% 3.93/1.00    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.93/1.00    inference(negated_conjecture,[],[f16])).
% 3.93/1.00  
% 3.93/1.00  fof(f35,plain,(
% 3.93/1.00    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 3.93/1.00    inference(ennf_transformation,[],[f17])).
% 3.93/1.00  
% 3.93/1.00  fof(f58,plain,(
% 3.93/1.00    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & r2_hidden(sK9,k1_funct_2(sK7,sK8)))),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f59,plain,(
% 3.93/1.00    (~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & r2_hidden(sK9,k1_funct_2(sK7,sK8))),
% 3.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f35,f58])).
% 3.93/1.00  
% 3.93/1.00  fof(f103,plain,(
% 3.93/1.00    r2_hidden(sK9,k1_funct_2(sK7,sK8))),
% 3.93/1.00    inference(cnf_transformation,[],[f59])).
% 3.93/1.00  
% 3.93/1.00  fof(f13,axiom,(
% 3.93/1.00    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f36,plain,(
% 3.93/1.00    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.93/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.93/1.00  
% 3.93/1.00  fof(f37,plain,(
% 3.93/1.00    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.93/1.00    inference(definition_folding,[],[f13,f36])).
% 3.93/1.00  
% 3.93/1.00  fof(f55,plain,(
% 3.93/1.00    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 3.93/1.00    inference(nnf_transformation,[],[f37])).
% 3.93/1.00  
% 3.93/1.00  fof(f92,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 3.93/1.00    inference(cnf_transformation,[],[f55])).
% 3.93/1.00  
% 3.93/1.00  fof(f110,plain,(
% 3.93/1.00    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 3.93/1.00    inference(equality_resolution,[],[f92])).
% 3.93/1.00  
% 3.93/1.00  fof(f49,plain,(
% 3.93/1.00    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.93/1.00    inference(nnf_transformation,[],[f36])).
% 3.93/1.00  
% 3.93/1.00  fof(f50,plain,(
% 3.93/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.93/1.00    inference(rectify,[],[f49])).
% 3.93/1.00  
% 3.93/1.00  fof(f53,plain,(
% 3.93/1.00    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) & k1_relat_1(sK5(X0,X1,X6)) = X1 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))))),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f52,plain,(
% 3.93/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) & k1_relat_1(sK4(X0,X1,X2)) = X1 & sK4(X0,X1,X2) = X3 & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))))) )),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f51,plain,(
% 3.93/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK3(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f54,plain,(
% 3.93/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) & k1_relat_1(sK4(X0,X1,X2)) = X1 & sK3(X0,X1,X2) = sK4(X0,X1,X2) & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) & k1_relat_1(sK5(X0,X1,X6)) = X1 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f50,f53,f52,f51])).
% 3.93/1.00  
% 3.93/1.00  fof(f82,plain,(
% 3.93/1.00    ( ! [X6,X2,X0,X1] : (sK5(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f54])).
% 3.93/1.00  
% 3.93/1.00  fof(f84,plain,(
% 3.93/1.00    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f54])).
% 3.93/1.00  
% 3.93/1.00  fof(f10,axiom,(
% 3.93/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f25,plain,(
% 3.93/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.93/1.00    inference(ennf_transformation,[],[f10])).
% 3.93/1.00  
% 3.93/1.00  fof(f26,plain,(
% 3.93/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.93/1.00    inference(flattening,[],[f25])).
% 3.93/1.00  
% 3.93/1.00  fof(f75,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f26])).
% 3.93/1.00  
% 3.93/1.00  fof(f83,plain,(
% 3.93/1.00    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK5(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f54])).
% 3.93/1.00  
% 3.93/1.00  fof(f12,axiom,(
% 3.93/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f29,plain,(
% 3.93/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.93/1.00    inference(ennf_transformation,[],[f12])).
% 3.93/1.00  
% 3.93/1.00  fof(f30,plain,(
% 3.93/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.93/1.00    inference(flattening,[],[f29])).
% 3.93/1.00  
% 3.93/1.00  fof(f79,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f30])).
% 3.93/1.00  
% 3.93/1.00  fof(f14,axiom,(
% 3.93/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f31,plain,(
% 3.93/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.93/1.00    inference(ennf_transformation,[],[f14])).
% 3.93/1.00  
% 3.93/1.00  fof(f32,plain,(
% 3.93/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.93/1.00    inference(flattening,[],[f31])).
% 3.93/1.00  
% 3.93/1.00  fof(f95,plain,(
% 3.93/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f32])).
% 3.93/1.00  
% 3.93/1.00  fof(f96,plain,(
% 3.93/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f32])).
% 3.93/1.00  
% 3.93/1.00  fof(f11,axiom,(
% 3.93/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f27,plain,(
% 3.93/1.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.00    inference(ennf_transformation,[],[f11])).
% 3.93/1.00  
% 3.93/1.00  fof(f28,plain,(
% 3.93/1.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.00    inference(flattening,[],[f27])).
% 3.93/1.00  
% 3.93/1.00  fof(f77,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f28])).
% 3.93/1.00  
% 3.93/1.00  fof(f104,plain,(
% 3.93/1.00    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)),
% 3.93/1.01    inference(cnf_transformation,[],[f59])).
% 3.93/1.01  
% 3.93/1.01  fof(f3,axiom,(
% 3.93/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f46,plain,(
% 3.93/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.93/1.01    inference(nnf_transformation,[],[f3])).
% 3.93/1.01  
% 3.93/1.01  fof(f47,plain,(
% 3.93/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.93/1.01    inference(flattening,[],[f46])).
% 3.93/1.01  
% 3.93/1.01  fof(f65,plain,(
% 3.93/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.93/1.01    inference(cnf_transformation,[],[f47])).
% 3.93/1.01  
% 3.93/1.01  fof(f106,plain,(
% 3.93/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.93/1.01    inference(equality_resolution,[],[f65])).
% 3.93/1.01  
% 3.93/1.01  fof(f67,plain,(
% 3.93/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f47])).
% 3.93/1.01  
% 3.93/1.01  fof(f81,plain,(
% 3.93/1.01    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f54])).
% 3.93/1.01  
% 3.93/1.01  fof(f80,plain,(
% 3.93/1.01    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f54])).
% 3.93/1.01  
% 3.93/1.01  fof(f7,axiom,(
% 3.93/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f22,plain,(
% 3.93/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.93/1.01    inference(ennf_transformation,[],[f7])).
% 3.93/1.01  
% 3.93/1.01  fof(f72,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f22])).
% 3.93/1.01  
% 3.93/1.01  fof(f2,axiom,(
% 3.93/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f18,plain,(
% 3.93/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.93/1.01    inference(ennf_transformation,[],[f2])).
% 3.93/1.01  
% 3.93/1.01  fof(f42,plain,(
% 3.93/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.93/1.01    inference(nnf_transformation,[],[f18])).
% 3.93/1.01  
% 3.93/1.01  fof(f43,plain,(
% 3.93/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.93/1.01    inference(rectify,[],[f42])).
% 3.93/1.01  
% 3.93/1.01  fof(f44,plain,(
% 3.93/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f45,plain,(
% 3.93/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.93/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 3.93/1.01  
% 3.93/1.01  fof(f63,plain,(
% 3.93/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f45])).
% 3.93/1.01  
% 3.93/1.01  fof(f1,axiom,(
% 3.93/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f38,plain,(
% 3.93/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.93/1.01    inference(nnf_transformation,[],[f1])).
% 3.93/1.01  
% 3.93/1.01  fof(f39,plain,(
% 3.93/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.93/1.01    inference(rectify,[],[f38])).
% 3.93/1.01  
% 3.93/1.01  fof(f40,plain,(
% 3.93/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f41,plain,(
% 3.93/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.93/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 3.93/1.01  
% 3.93/1.01  fof(f60,plain,(
% 3.93/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f41])).
% 3.93/1.01  
% 3.93/1.01  fof(f5,axiom,(
% 3.93/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f48,plain,(
% 3.93/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.93/1.01    inference(nnf_transformation,[],[f5])).
% 3.93/1.01  
% 3.93/1.01  fof(f70,plain,(
% 3.93/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f48])).
% 3.93/1.01  
% 3.93/1.01  fof(f9,axiom,(
% 3.93/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f24,plain,(
% 3.93/1.01    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.01    inference(ennf_transformation,[],[f9])).
% 3.93/1.01  
% 3.93/1.01  fof(f74,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/1.01    inference(cnf_transformation,[],[f24])).
% 3.93/1.01  
% 3.93/1.01  fof(f8,axiom,(
% 3.93/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f23,plain,(
% 3.93/1.01    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.93/1.01    inference(ennf_transformation,[],[f8])).
% 3.93/1.01  
% 3.93/1.01  fof(f73,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.93/1.01    inference(cnf_transformation,[],[f23])).
% 3.93/1.01  
% 3.93/1.01  fof(f69,plain,(
% 3.93/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.93/1.01    inference(cnf_transformation,[],[f48])).
% 3.93/1.01  
% 3.93/1.01  fof(f15,axiom,(
% 3.93/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f33,plain,(
% 3.93/1.01    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.93/1.01    inference(ennf_transformation,[],[f15])).
% 3.93/1.01  
% 3.93/1.01  fof(f34,plain,(
% 3.93/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.93/1.01    inference(flattening,[],[f33])).
% 3.93/1.01  
% 3.93/1.01  fof(f56,plain,(
% 3.93/1.01    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 3.93/1.01    introduced(choice_axiom,[])).
% 3.93/1.01  
% 3.93/1.01  fof(f57,plain,(
% 3.93/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.93/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f56])).
% 3.93/1.01  
% 3.93/1.01  fof(f99,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK6(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f57])).
% 3.93/1.01  
% 3.93/1.01  fof(f114,plain,(
% 3.93/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.93/1.01    inference(equality_resolution,[],[f99])).
% 3.93/1.01  
% 3.93/1.01  fof(f6,axiom,(
% 3.93/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.93/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.01  
% 3.93/1.01  fof(f21,plain,(
% 3.93/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.93/1.01    inference(ennf_transformation,[],[f6])).
% 3.93/1.01  
% 3.93/1.01  fof(f71,plain,(
% 3.93/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.93/1.01    inference(cnf_transformation,[],[f21])).
% 3.93/1.01  
% 3.93/1.01  cnf(c_44,negated_conjecture,
% 3.93/1.01      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
% 3.93/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6652,plain,
% 3.93/1.01      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_33,plain,
% 3.93/1.01      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 3.93/1.01      inference(cnf_transformation,[],[f110]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6656,plain,
% 3.93/1.01      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_29,plain,
% 3.93/1.01      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK5(X0,X1,X3) = X3 ),
% 3.93/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6660,plain,
% 3.93/1.01      ( sK5(X0,X1,X2) = X2
% 3.93/1.01      | sP0(X0,X1,X3) != iProver_top
% 3.93/1.01      | r2_hidden(X2,X3) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_9281,plain,
% 3.93/1.01      ( sK5(X0,X1,X2) = X2
% 3.93/1.01      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6656,c_6660]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_9406,plain,
% 3.93/1.01      ( sK5(sK8,sK7,sK9) = sK9 ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6652,c_9281]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_27,plain,
% 3.93/1.01      ( ~ sP0(X0,X1,X2)
% 3.93/1.01      | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0)
% 3.93/1.01      | ~ r2_hidden(X3,X2) ),
% 3.93/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6662,plain,
% 3.93/1.01      ( sP0(X0,X1,X2) != iProver_top
% 3.93/1.01      | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) = iProver_top
% 3.93/1.01      | r2_hidden(X3,X2) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_9953,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) = iProver_top
% 3.93/1.01      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6656,c_6662]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_20176,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top
% 3.93/1.01      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_9406,c_9953]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_45,plain,
% 3.93/1.01      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_20470,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_20176,c_45]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_15,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.93/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.93/1.01      | ~ v1_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6670,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.93/1.01      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.93/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.93/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_28,plain,
% 3.93/1.01      ( ~ sP0(X0,X1,X2)
% 3.93/1.01      | ~ r2_hidden(X3,X2)
% 3.93/1.01      | k1_relat_1(sK5(X0,X1,X3)) = X1 ),
% 3.93/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6661,plain,
% 3.93/1.01      ( k1_relat_1(sK5(X0,X1,X2)) = X1
% 3.93/1.01      | sP0(X0,X1,X3) != iProver_top
% 3.93/1.01      | r2_hidden(X2,X3) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_9399,plain,
% 3.93/1.01      ( k1_relat_1(sK5(X0,X1,X2)) = X1
% 3.93/1.01      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6656,c_6661]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11042,plain,
% 3.93/1.01      ( k1_relat_1(sK5(sK8,sK7,sK9)) = sK7 ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6652,c_9399]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11053,plain,
% 3.93/1.01      ( k1_relat_1(sK9) = sK7 ),
% 3.93/1.01      inference(light_normalisation,[status(thm)],[c_11042,c_9406]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_18,plain,
% 3.93/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.93/1.01      | v1_partfun1(X0,X1)
% 3.93/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | v1_xboole_0(X2) ),
% 3.93/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_35,plain,
% 3.93/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_567,plain,
% 3.93/1.01      ( v1_partfun1(X0,X1)
% 3.93/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_funct_1(X3)
% 3.93/1.01      | ~ v1_relat_1(X3)
% 3.93/1.01      | v1_xboole_0(X2)
% 3.93/1.01      | X3 != X0
% 3.93/1.01      | k2_relat_1(X3) != X2
% 3.93/1.01      | k1_relat_1(X3) != X1 ),
% 3.93/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_568,plain,
% 3.93/1.01      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.93/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0)
% 3.93/1.01      | v1_xboole_0(k2_relat_1(X0)) ),
% 3.93/1.01      inference(unflattening,[status(thm)],[c_567]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_34,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_572,plain,
% 3.93/1.01      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0)
% 3.93/1.01      | v1_xboole_0(k2_relat_1(X0)) ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_568,c_34]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_16,plain,
% 3.93/1.01      ( v1_funct_2(X0,X1,X2)
% 3.93/1.01      | ~ v1_partfun1(X0,X1)
% 3.93/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.01      | ~ v1_funct_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_43,negated_conjecture,
% 3.93/1.01      ( ~ v1_funct_2(sK9,sK7,sK8)
% 3.93/1.01      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 3.93/1.01      | ~ v1_funct_1(sK9) ),
% 3.93/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_647,plain,
% 3.93/1.01      ( ~ v1_partfun1(X0,X1)
% 3.93/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.01      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_funct_1(sK9)
% 3.93/1.01      | sK8 != X2
% 3.93/1.01      | sK7 != X1
% 3.93/1.01      | sK9 != X0 ),
% 3.93/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_43]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_648,plain,
% 3.93/1.01      ( ~ v1_partfun1(sK9,sK7)
% 3.93/1.01      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 3.93/1.01      | ~ v1_funct_1(sK9) ),
% 3.93/1.01      inference(unflattening,[status(thm)],[c_647]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_800,plain,
% 3.93/1.01      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_funct_1(sK9)
% 3.93/1.01      | ~ v1_relat_1(X0)
% 3.93/1.01      | v1_xboole_0(k2_relat_1(X0))
% 3.93/1.01      | k1_relat_1(X0) != sK7
% 3.93/1.01      | sK9 != X0 ),
% 3.93/1.01      inference(resolution_lifted,[status(thm)],[c_572,c_648]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_801,plain,
% 3.93/1.01      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 3.93/1.01      | ~ v1_funct_1(sK9)
% 3.93/1.01      | ~ v1_relat_1(sK9)
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9))
% 3.93/1.01      | k1_relat_1(sK9) != sK7 ),
% 3.93/1.01      inference(unflattening,[status(thm)],[c_800]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6644,plain,
% 3.93/1.01      ( k1_relat_1(sK9) != sK7
% 3.93/1.01      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 3.93/1.01      | v1_funct_1(sK9) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11206,plain,
% 3.93/1.01      ( sK7 != sK7
% 3.93/1.01      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 3.93/1.01      | v1_funct_1(sK9) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(demodulation,[status(thm)],[c_11053,c_6644]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11252,plain,
% 3.93/1.01      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 3.93/1.01      | v1_funct_1(sK9) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(equality_resolution_simp,[status(thm)],[c_11206]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7,plain,
% 3.93/1.01      ( r1_tarski(X0,X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f106]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_139,plain,
% 3.93/1.01      ( r1_tarski(sK9,sK9) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_5,plain,
% 3.93/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.93/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_143,plain,
% 3.93/1.01      ( ~ r1_tarski(sK9,sK9) | sK9 = sK9 ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_802,plain,
% 3.93/1.01      ( k1_relat_1(sK9) != sK7
% 3.93/1.01      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 3.93/1.01      | v1_funct_1(sK9) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_30,plain,
% 3.93/1.01      ( ~ sP0(X0,X1,X2)
% 3.93/1.01      | ~ r2_hidden(X3,X2)
% 3.93/1.01      | v1_funct_1(sK5(X0,X1,X3)) ),
% 3.93/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7051,plain,
% 3.93/1.01      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 3.93/1.01      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 3.93/1.01      | v1_funct_1(sK5(X0,X1,sK9)) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7207,plain,
% 3.93/1.01      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 3.93/1.01      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 3.93/1.01      | v1_funct_1(sK5(sK8,sK7,sK9)) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7051]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7209,plain,
% 3.93/1.01      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
% 3.93/1.01      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
% 3.93/1.01      | v1_funct_1(sK5(sK8,sK7,sK9)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_7207]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7208,plain,
% 3.93/1.01      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_33]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7211,plain,
% 3.93/1.01      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_7208]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_5743,plain,
% 3.93/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.93/1.01      theory(equality) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7399,plain,
% 3.93/1.01      ( v1_funct_1(X0)
% 3.93/1.01      | ~ v1_funct_1(sK5(sK8,sK7,sK9))
% 3.93/1.01      | X0 != sK5(sK8,sK7,sK9) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_5743]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7400,plain,
% 3.93/1.01      ( X0 != sK5(sK8,sK7,sK9)
% 3.93/1.01      | v1_funct_1(X0) = iProver_top
% 3.93/1.01      | v1_funct_1(sK5(sK8,sK7,sK9)) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_7399]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7402,plain,
% 3.93/1.01      ( sK9 != sK5(sK8,sK7,sK9)
% 3.93/1.01      | v1_funct_1(sK5(sK8,sK7,sK9)) != iProver_top
% 3.93/1.01      | v1_funct_1(sK9) = iProver_top ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7400]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_31,plain,
% 3.93/1.01      ( ~ sP0(X0,X1,X2)
% 3.93/1.01      | ~ r2_hidden(X3,X2)
% 3.93/1.01      | v1_relat_1(sK5(X0,X1,X3)) ),
% 3.93/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7056,plain,
% 3.93/1.01      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 3.93/1.01      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 3.93/1.01      | v1_relat_1(sK5(X0,X1,sK9)) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_31]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7432,plain,
% 3.93/1.01      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 3.93/1.01      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 3.93/1.01      | v1_relat_1(sK5(sK8,sK7,sK9)) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7056]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7434,plain,
% 3.93/1.01      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
% 3.93/1.01      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
% 3.93/1.01      | v1_relat_1(sK5(sK8,sK7,sK9)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_7432]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7093,plain,
% 3.93/1.01      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 3.93/1.01      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 3.93/1.01      | sK5(X0,X1,sK9) = sK9 ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7431,plain,
% 3.93/1.01      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 3.93/1.01      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 3.93/1.01      | sK5(sK8,sK7,sK9) = sK9 ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7093]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_5733,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7698,plain,
% 3.93/1.01      ( X0 != X1 | X0 = sK5(sK8,sK7,sK9) | sK5(sK8,sK7,sK9) != X1 ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_5733]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7699,plain,
% 3.93/1.01      ( sK5(sK8,sK7,sK9) != sK9 | sK9 = sK5(sK8,sK7,sK9) | sK9 != sK9 ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7698]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_5742,plain,
% 3.93/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.93/1.01      theory(equality) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7993,plain,
% 3.93/1.01      ( v1_relat_1(X0)
% 3.93/1.01      | ~ v1_relat_1(sK5(sK8,sK7,sK9))
% 3.93/1.01      | X0 != sK5(sK8,sK7,sK9) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_5742]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7999,plain,
% 3.93/1.01      ( X0 != sK5(sK8,sK7,sK9)
% 3.93/1.01      | v1_relat_1(X0) = iProver_top
% 3.93/1.01      | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_7993]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_8001,plain,
% 3.93/1.01      ( sK9 != sK5(sK8,sK7,sK9)
% 3.93/1.01      | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) = iProver_top ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7999]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_17497,plain,
% 3.93/1.01      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_11252,c_44,c_45,c_139,c_143,c_802,c_7209,c_7208,
% 3.93/1.01                 c_7211,c_7402,c_7434,c_7431,c_7699,c_8001,c_11053]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_17504,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | r1_tarski(k1_relat_1(sK9),sK7) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6670,c_17497]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_17511,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | r1_tarski(sK7,sK7) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(light_normalisation,[status(thm)],[c_17504,c_11053]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_17825,plain,
% 3.93/1.01      ( r1_tarski(sK7,sK7) != iProver_top
% 3.93/1.01      | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_17511,c_44,c_45,c_139,c_143,c_7208,c_7211,c_7434,
% 3.93/1.01                 c_7431,c_7699,c_8001]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_17826,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | r1_tarski(sK7,sK7) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(renaming,[status(thm)],[c_17825]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6677,plain,
% 3.93/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_17832,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(forward_subsumption_resolution,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_17826,c_6677]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_20481,plain,
% 3.93/1.01      ( v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_20470,c_17832]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6655,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.93/1.01      | v1_funct_1(X0) != iProver_top
% 3.93/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11364,plain,
% 3.93/1.01      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top
% 3.93/1.01      | v1_funct_1(sK9) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_11053,c_6655]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11471,plain,
% 3.93/1.01      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_11364,c_44,c_45,c_139,c_143,c_7209,c_7208,c_7211,
% 3.93/1.01                 c_7402,c_7434,c_7431,c_7699,c_8001]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.01      | ~ v1_xboole_0(X2)
% 3.93/1.01      | v1_xboole_0(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6673,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.93/1.01      | v1_xboole_0(X2) != iProver_top
% 3.93/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11478,plain,
% 3.93/1.01      ( v1_xboole_0(k2_relat_1(sK9)) != iProver_top
% 3.93/1.01      | v1_xboole_0(sK9) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_11471,c_6673]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_21086,plain,
% 3.93/1.01      ( v1_xboole_0(sK9) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_20481,c_11478]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_3,plain,
% 3.93/1.01      ( r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6680,plain,
% 3.93/1.01      ( r1_tarski(X0,X1) = iProver_top
% 3.93/1.01      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_1,plain,
% 3.93/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.93/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6682,plain,
% 3.93/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.93/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7829,plain,
% 3.93/1.01      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6680,c_6682]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_9,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.93/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6675,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.93/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_14,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6671,plain,
% 3.93/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.93/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7977,plain,
% 3.93/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.93/1.01      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6675,c_6671]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_8165,plain,
% 3.93/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.93/1.01      | v1_xboole_0(X2) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_7829,c_7977]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_24489,plain,
% 3.93/1.01      ( k1_relset_1(X0,X1,sK9) = k1_relat_1(sK9) ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_21086,c_8165]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_24491,plain,
% 3.93/1.01      ( k1_relset_1(X0,X1,sK9) = sK7 ),
% 3.93/1.01      inference(light_normalisation,[status(thm)],[c_24489,c_11053]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_13,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.93/1.01      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.93/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6672,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.93/1.01      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_10,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.93/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6674,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.93/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_8504,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.93/1.01      | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6672,c_6674]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_9053,plain,
% 3.93/1.01      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.93/1.01      | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6675,c_8504]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_24509,plain,
% 3.93/1.01      ( r1_tarski(sK7,X0) = iProver_top
% 3.93/1.01      | r1_tarski(sK9,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_24491,c_9053]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_24542,plain,
% 3.93/1.01      ( r1_tarski(sK7,sK9) = iProver_top
% 3.93/1.01      | r1_tarski(sK9,k2_zfmisc_1(sK9,sK9)) != iProver_top ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_24509]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_8628,plain,
% 3.93/1.01      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.93/1.01      | v1_xboole_0(X2) != iProver_top
% 3.93/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6675,c_6673]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_20259,plain,
% 3.93/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.93/1.01      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6677,c_8628]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6678,plain,
% 3.93/1.01      ( X0 = X1
% 3.93/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.93/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_8057,plain,
% 3.93/1.01      ( X0 = X1
% 3.93/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.93/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_7829,c_6678]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_8270,plain,
% 3.93/1.01      ( X0 = X1
% 3.93/1.01      | v1_xboole_0(X1) != iProver_top
% 3.93/1.01      | v1_xboole_0(X0) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_7829,c_8057]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_21715,plain,
% 3.93/1.01      ( k2_zfmisc_1(X0,X1) = X2
% 3.93/1.01      | v1_xboole_0(X2) != iProver_top
% 3.93/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_20259,c_8270]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_21733,plain,
% 3.93/1.01      ( k2_zfmisc_1(sK9,sK9) = sK9 | v1_xboole_0(sK9) != iProver_top ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_21715]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_14731,plain,
% 3.93/1.01      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_5733]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_14732,plain,
% 3.93/1.01      ( k2_zfmisc_1(sK9,sK9) != sK9
% 3.93/1.01      | sK9 = k2_zfmisc_1(sK9,sK9)
% 3.93/1.01      | sK9 != sK9 ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_14731]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_40,plain,
% 3.93/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.93/1.01      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_relat_1(X0) ),
% 3.93/1.01      inference(cnf_transformation,[],[f114]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_679,plain,
% 3.93/1.01      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 3.93/1.01      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 3.93/1.01      | ~ v1_funct_1(X0)
% 3.93/1.01      | ~ v1_funct_1(sK9)
% 3.93/1.01      | ~ v1_relat_1(X0)
% 3.93/1.01      | k1_relat_1(X0) != sK7
% 3.93/1.01      | sK8 != X1
% 3.93/1.01      | sK9 != X0 ),
% 3.93/1.01      inference(resolution_lifted,[status(thm)],[c_40,c_43]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_680,plain,
% 3.93/1.01      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 3.93/1.01      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
% 3.93/1.01      | ~ v1_funct_1(sK9)
% 3.93/1.01      | ~ v1_relat_1(sK9)
% 3.93/1.01      | k1_relat_1(sK9) != sK7 ),
% 3.93/1.01      inference(unflattening,[status(thm)],[c_679]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6649,plain,
% 3.93/1.01      ( k1_relat_1(sK9) != sK7
% 3.93/1.01      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 3.93/1.01      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9)) = iProver_top
% 3.93/1.01      | v1_funct_1(sK9) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11210,plain,
% 3.93/1.01      ( sK7 != sK7
% 3.93/1.01      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 3.93/1.01      | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
% 3.93/1.01      | v1_funct_1(sK9) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top ),
% 3.93/1.01      inference(demodulation,[status(thm)],[c_11053,c_6649]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11221,plain,
% 3.93/1.01      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 3.93/1.01      | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
% 3.93/1.01      | v1_funct_1(sK9) != iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top ),
% 3.93/1.01      inference(equality_resolution_simp,[status(thm)],[c_11210]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12582,plain,
% 3.93/1.01      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 3.93/1.01      | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_11221,c_44,c_45,c_139,c_143,c_7209,c_7208,c_7211,
% 3.93/1.01                 c_7402,c_7434,c_7431,c_7699,c_8001]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12589,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | r1_tarski(k1_relat_1(sK9),sK7) != iProver_top
% 3.93/1.01      | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_6670,c_12582]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12594,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | r1_tarski(sK7,sK7) != iProver_top
% 3.93/1.01      | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
% 3.93/1.01      | v1_relat_1(sK9) != iProver_top ),
% 3.93/1.01      inference(light_normalisation,[status(thm)],[c_12589,c_11053]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12842,plain,
% 3.93/1.01      ( r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top
% 3.93/1.01      | r1_tarski(sK7,sK7) != iProver_top
% 3.93/1.01      | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
% 3.93/1.01      inference(global_propositional_subsumption,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_12594,c_44,c_45,c_139,c_143,c_7208,c_7211,c_7434,
% 3.93/1.01                 c_7431,c_7699,c_8001]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12843,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | r1_tarski(sK7,sK7) != iProver_top
% 3.93/1.01      | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top ),
% 3.93/1.01      inference(renaming,[status(thm)],[c_12842]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12849,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | r2_hidden(sK6(sK7,sK8,sK9),sK7) = iProver_top ),
% 3.93/1.01      inference(forward_subsumption_resolution,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_12843,c_6677]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_11,plain,
% 3.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.93/1.01      | ~ r2_hidden(X2,X0)
% 3.93/1.01      | ~ v1_xboole_0(X1) ),
% 3.93/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_334,plain,
% 3.93/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.93/1.01      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_335,plain,
% 3.93/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.93/1.01      inference(renaming,[status(thm)],[c_334]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_403,plain,
% 3.93/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 3.93/1.01      inference(bin_hyper_res,[status(thm)],[c_11,c_335]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_6651,plain,
% 3.93/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.93/1.01      | r2_hidden(X2,X0) != iProver_top
% 3.93/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12853,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | r1_tarski(sK7,X0) != iProver_top
% 3.93/1.01      | v1_xboole_0(X0) != iProver_top ),
% 3.93/1.01      inference(superposition,[status(thm)],[c_12849,c_6651]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_12875,plain,
% 3.93/1.01      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 3.93/1.01      | r1_tarski(sK7,sK9) != iProver_top
% 3.93/1.01      | v1_xboole_0(sK9) != iProver_top ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_12853]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_5736,plain,
% 3.93/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.93/1.01      theory(equality) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7297,plain,
% 3.93/1.01      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.93/1.01      | r1_tarski(X3,k2_zfmisc_1(X1,X2))
% 3.93/1.01      | X3 != X0 ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_5736]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_10318,plain,
% 3.93/1.01      ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.93/1.01      | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2))
% 3.93/1.01      | X0 != k2_zfmisc_1(X1,X2) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7297]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_10319,plain,
% 3.93/1.01      ( X0 != k2_zfmisc_1(X1,X2)
% 3.93/1.01      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 3.93/1.01      | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_10318]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_10321,plain,
% 3.93/1.01      ( sK9 != k2_zfmisc_1(sK9,sK9)
% 3.93/1.01      | r1_tarski(k2_zfmisc_1(sK9,sK9),k2_zfmisc_1(sK9,sK9)) != iProver_top
% 3.93/1.01      | r1_tarski(sK9,k2_zfmisc_1(sK9,sK9)) = iProver_top ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_10319]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7288,plain,
% 3.93/1.01      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7293,plain,
% 3.93/1.01      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.93/1.01      inference(predicate_to_equality,[status(thm)],[c_7288]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(c_7295,plain,
% 3.93/1.01      ( r1_tarski(k2_zfmisc_1(sK9,sK9),k2_zfmisc_1(sK9,sK9)) = iProver_top ),
% 3.93/1.01      inference(instantiation,[status(thm)],[c_7293]) ).
% 3.93/1.01  
% 3.93/1.01  cnf(contradiction,plain,
% 3.93/1.01      ( $false ),
% 3.93/1.01      inference(minisat,
% 3.93/1.01                [status(thm)],
% 3.93/1.01                [c_24542,c_21733,c_20176,c_17832,c_14732,c_12875,c_11478,
% 3.93/1.01                 c_10321,c_7295,c_143,c_139,c_45]) ).
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/1.01  
% 3.93/1.01  ------                               Statistics
% 3.93/1.01  
% 3.93/1.01  ------ General
% 3.93/1.01  
% 3.93/1.01  abstr_ref_over_cycles:                  0
% 3.93/1.01  abstr_ref_under_cycles:                 0
% 3.93/1.01  gc_basic_clause_elim:                   0
% 3.93/1.01  forced_gc_time:                         0
% 3.93/1.01  parsing_time:                           0.007
% 3.93/1.01  unif_index_cands_time:                  0.
% 3.93/1.01  unif_index_add_time:                    0.
% 3.93/1.01  orderings_time:                         0.
% 3.93/1.01  out_proof_time:                         0.013
% 3.93/1.01  total_time:                             0.462
% 3.93/1.01  num_of_symbols:                         58
% 3.93/1.01  num_of_terms:                           16769
% 3.93/1.01  
% 3.93/1.01  ------ Preprocessing
% 3.93/1.01  
% 3.93/1.01  num_of_splits:                          2
% 3.93/1.01  num_of_split_atoms:                     2
% 3.93/1.01  num_of_reused_defs:                     0
% 3.93/1.01  num_eq_ax_congr_red:                    54
% 3.93/1.01  num_of_sem_filtered_clauses:            1
% 3.93/1.01  num_of_subtypes:                        0
% 3.93/1.01  monotx_restored_types:                  0
% 3.93/1.01  sat_num_of_epr_types:                   0
% 3.93/1.01  sat_num_of_non_cyclic_types:            0
% 3.93/1.01  sat_guarded_non_collapsed_types:        0
% 3.93/1.01  num_pure_diseq_elim:                    0
% 3.93/1.01  simp_replaced_by:                       0
% 3.93/1.01  res_preprocessed:                       192
% 3.93/1.01  prep_upred:                             0
% 3.93/1.01  prep_unflattend:                        172
% 3.93/1.01  smt_new_axioms:                         0
% 3.93/1.01  pred_elim_cands:                        7
% 3.93/1.01  pred_elim:                              2
% 3.93/1.01  pred_elim_cl:                           1
% 3.93/1.01  pred_elim_cycles:                       9
% 3.93/1.01  merged_defs:                            8
% 3.93/1.01  merged_defs_ncl:                        0
% 3.93/1.01  bin_hyper_res:                          9
% 3.93/1.01  prep_cycles:                            4
% 3.93/1.01  pred_elim_time:                         0.057
% 3.93/1.01  splitting_time:                         0.
% 3.93/1.01  sem_filter_time:                        0.
% 3.93/1.01  monotx_time:                            0.
% 3.93/1.01  subtype_inf_time:                       0.
% 3.93/1.01  
% 3.93/1.01  ------ Problem properties
% 3.93/1.01  
% 3.93/1.01  clauses:                                40
% 3.93/1.01  conjectures:                            1
% 3.93/1.01  epr:                                    6
% 3.93/1.01  horn:                                   31
% 3.93/1.01  ground:                                 6
% 3.93/1.01  unary:                                  3
% 3.93/1.01  binary:                                 10
% 3.93/1.01  lits:                                   122
% 3.93/1.01  lits_eq:                                14
% 3.93/1.01  fd_pure:                                0
% 3.93/1.01  fd_pseudo:                              0
% 3.93/1.01  fd_cond:                                0
% 3.93/1.01  fd_pseudo_cond:                         2
% 3.93/1.01  ac_symbols:                             0
% 3.93/1.01  
% 3.93/1.01  ------ Propositional Solver
% 3.93/1.01  
% 3.93/1.01  prop_solver_calls:                      28
% 3.93/1.01  prop_fast_solver_calls:                 2938
% 3.93/1.01  smt_solver_calls:                       0
% 3.93/1.01  smt_fast_solver_calls:                  0
% 3.93/1.01  prop_num_of_clauses:                    7388
% 3.93/1.01  prop_preprocess_simplified:             16859
% 3.93/1.01  prop_fo_subsumed:                       95
% 3.93/1.01  prop_solver_time:                       0.
% 3.93/1.01  smt_solver_time:                        0.
% 3.93/1.01  smt_fast_solver_time:                   0.
% 3.93/1.01  prop_fast_solver_time:                  0.
% 3.93/1.01  prop_unsat_core_time:                   0.
% 3.93/1.01  
% 3.93/1.01  ------ QBF
% 3.93/1.01  
% 3.93/1.01  qbf_q_res:                              0
% 3.93/1.01  qbf_num_tautologies:                    0
% 3.93/1.01  qbf_prep_cycles:                        0
% 3.93/1.01  
% 3.93/1.01  ------ BMC1
% 3.93/1.01  
% 3.93/1.01  bmc1_current_bound:                     -1
% 3.93/1.01  bmc1_last_solved_bound:                 -1
% 3.93/1.01  bmc1_unsat_core_size:                   -1
% 3.93/1.01  bmc1_unsat_core_parents_size:           -1
% 3.93/1.01  bmc1_merge_next_fun:                    0
% 3.93/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.93/1.01  
% 3.93/1.01  ------ Instantiation
% 3.93/1.01  
% 3.93/1.01  inst_num_of_clauses:                    1724
% 3.93/1.01  inst_num_in_passive:                    333
% 3.93/1.01  inst_num_in_active:                     666
% 3.93/1.01  inst_num_in_unprocessed:                725
% 3.93/1.01  inst_num_of_loops:                      900
% 3.93/1.01  inst_num_of_learning_restarts:          0
% 3.93/1.01  inst_num_moves_active_passive:          231
% 3.93/1.01  inst_lit_activity:                      0
% 3.93/1.01  inst_lit_activity_moves:                0
% 3.93/1.01  inst_num_tautologies:                   0
% 3.93/1.01  inst_num_prop_implied:                  0
% 3.93/1.01  inst_num_existing_simplified:           0
% 3.93/1.01  inst_num_eq_res_simplified:             0
% 3.93/1.01  inst_num_child_elim:                    0
% 3.93/1.01  inst_num_of_dismatching_blockings:      1087
% 3.93/1.01  inst_num_of_non_proper_insts:           2065
% 3.93/1.01  inst_num_of_duplicates:                 0
% 3.93/1.01  inst_inst_num_from_inst_to_res:         0
% 3.93/1.01  inst_dismatching_checking_time:         0.
% 3.93/1.01  
% 3.93/1.01  ------ Resolution
% 3.93/1.01  
% 3.93/1.01  res_num_of_clauses:                     0
% 3.93/1.01  res_num_in_passive:                     0
% 3.93/1.01  res_num_in_active:                      0
% 3.93/1.01  res_num_of_loops:                       196
% 3.93/1.01  res_forward_subset_subsumed:            113
% 3.93/1.01  res_backward_subset_subsumed:           4
% 3.93/1.01  res_forward_subsumed:                   0
% 3.93/1.01  res_backward_subsumed:                  1
% 3.93/1.01  res_forward_subsumption_resolution:     3
% 3.93/1.01  res_backward_subsumption_resolution:    0
% 3.93/1.01  res_clause_to_clause_subsumption:       1714
% 3.93/1.01  res_orphan_elimination:                 0
% 3.93/1.01  res_tautology_del:                      250
% 3.93/1.01  res_num_eq_res_simplified:              0
% 3.93/1.01  res_num_sel_changes:                    0
% 3.93/1.01  res_moves_from_active_to_pass:          0
% 3.93/1.01  
% 3.93/1.01  ------ Superposition
% 3.93/1.01  
% 3.93/1.01  sup_time_total:                         0.
% 3.93/1.01  sup_time_generating:                    0.
% 3.93/1.01  sup_time_sim_full:                      0.
% 3.93/1.01  sup_time_sim_immed:                     0.
% 3.93/1.01  
% 3.93/1.01  sup_num_of_clauses:                     399
% 3.93/1.01  sup_num_in_active:                      157
% 3.93/1.01  sup_num_in_passive:                     242
% 3.93/1.01  sup_num_of_loops:                       179
% 3.93/1.01  sup_fw_superposition:                   172
% 3.93/1.01  sup_bw_superposition:                   359
% 3.93/1.01  sup_immediate_simplified:               109
% 3.93/1.01  sup_given_eliminated:                   0
% 3.93/1.01  comparisons_done:                       0
% 3.93/1.01  comparisons_avoided:                    0
% 3.93/1.01  
% 3.93/1.01  ------ Simplifications
% 3.93/1.01  
% 3.93/1.01  
% 3.93/1.01  sim_fw_subset_subsumed:                 43
% 3.93/1.01  sim_bw_subset_subsumed:                 10
% 3.93/1.01  sim_fw_subsumed:                        28
% 3.93/1.01  sim_bw_subsumed:                        0
% 3.93/1.01  sim_fw_subsumption_res:                 5
% 3.93/1.01  sim_bw_subsumption_res:                 0
% 3.93/1.01  sim_tautology_del:                      6
% 3.93/1.01  sim_eq_tautology_del:                   10
% 3.93/1.01  sim_eq_res_simp:                        5
% 3.93/1.01  sim_fw_demodulated:                     1
% 3.93/1.01  sim_bw_demodulated:                     22
% 3.93/1.01  sim_light_normalised:                   45
% 3.93/1.01  sim_joinable_taut:                      0
% 3.93/1.01  sim_joinable_simp:                      0
% 3.93/1.01  sim_ac_normalised:                      0
% 3.93/1.01  sim_smt_subsumption:                    0
% 3.93/1.01  
%------------------------------------------------------------------------------

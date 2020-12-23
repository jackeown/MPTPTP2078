%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:13 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  203 (4485 expanded)
%              Number of clauses        :  129 (1586 expanded)
%              Number of leaves         :   24 (1122 expanded)
%              Depth                    :   29
%              Number of atoms          :  735 (27202 expanded)
%              Number of equality atoms :  261 (8175 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        | ~ v1_funct_2(sK7,sK5,sK6)
        | ~ v1_funct_1(sK7) )
      & r2_hidden(sK7,k1_funct_2(sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7) )
    & r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f34,f52])).

fof(f91,plain,(
    r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f35,plain,(
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

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f13,f35])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f86])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f49,f48,f47])).

fof(f76,plain,(
    ! [X6,X2,X0,X1] :
      ( sK4(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK4(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f89,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
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

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_38,negated_conjecture,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5261,plain,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_33,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_5263,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK4(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5267,plain,
    ( sK4(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6289,plain,
    ( sK4(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5263,c_5267])).

cnf(c_6557,plain,
    ( sK4(sK6,sK5,sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_5261,c_6289])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5269,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7520,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(sK4(X2,X1,X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5263,c_5269])).

cnf(c_9981,plain,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6557,c_7520])).

cnf(c_39,plain,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_10162,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9981,c_39])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5277,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK4(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5268,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6855,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5263,c_5268])).

cnf(c_7244,plain,
    ( k1_relat_1(sK4(sK6,sK5,sK7)) = sK5 ),
    inference(superposition,[status(thm)],[c_5261,c_6855])).

cnf(c_7246,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_7244,c_6557])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_552,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_553,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_557,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_34])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,negated_conjecture,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_576,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | sK6 != X2
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_37])).

cnf(c_577,plain,
    ( ~ v1_partfun1(sK7,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_641,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK5
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_557,c_577])).

cnf(c_642,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | v1_xboole_0(k2_relat_1(sK7))
    | k1_relat_1(sK7) != sK5 ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_5255,plain,
    ( k1_relat_1(sK7) != sK5
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_7270,plain,
    ( sK5 != sK5
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7246,c_5255])).

cnf(c_7281,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7270])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_125,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_129,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_643,plain,
    ( k1_relat_1(sK7) != sK5
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5561,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | v1_funct_1(sK4(X0,X1,sK7)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_5667,plain,
    ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | v1_funct_1(sK4(sK6,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_5561])).

cnf(c_5669,plain,
    ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) != iProver_top
    | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
    | v1_funct_1(sK4(sK6,sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5667])).

cnf(c_5668,plain,
    ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_5671,plain,
    ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5668])).

cnf(c_4506,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5762,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK4(sK6,sK5,sK7))
    | X0 != sK4(sK6,sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_4506])).

cnf(c_5763,plain,
    ( X0 != sK4(sK6,sK5,sK7)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4(sK6,sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5762])).

cnf(c_5765,plain,
    ( sK7 != sK4(sK6,sK5,sK7)
    | v1_funct_1(sK4(sK6,sK5,sK7)) != iProver_top
    | v1_funct_1(sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5763])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5575,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | v1_relat_1(sK4(X0,X1,sK7)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_5782,plain,
    ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | v1_relat_1(sK4(sK6,sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_5575])).

cnf(c_5784,plain,
    ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) != iProver_top
    | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
    | v1_relat_1(sK4(sK6,sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5782])).

cnf(c_5606,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | sK4(X0,X1,sK7) = sK7 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_5781,plain,
    ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
    | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | sK4(sK6,sK5,sK7) = sK7 ),
    inference(instantiation,[status(thm)],[c_5606])).

cnf(c_4503,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5910,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK4(sK6,sK5,sK7))
    | X0 != sK4(sK6,sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_4503])).

cnf(c_5921,plain,
    ( X0 != sK4(sK6,sK5,sK7)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK4(sK6,sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5910])).

cnf(c_5923,plain,
    ( sK7 != sK4(sK6,sK5,sK7)
    | v1_relat_1(sK4(sK6,sK5,sK7)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5921])).

cnf(c_4496,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6007,plain,
    ( X0 != X1
    | X0 = sK4(sK6,sK5,sK7)
    | sK4(sK6,sK5,sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_4496])).

cnf(c_6008,plain,
    ( sK4(sK6,sK5,sK7) != sK7
    | sK7 = sK4(sK6,sK5,sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_6007])).

cnf(c_8763,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7281,c_38,c_39,c_125,c_129,c_643,c_5669,c_5668,c_5671,c_5765,c_5784,c_5781,c_5923,c_6008,c_7246])).

cnf(c_8770,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5277,c_8763])).

cnf(c_8775,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8770,c_7246])).

cnf(c_8866,plain,
    ( r1_tarski(sK5,sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8775,c_38,c_39,c_125,c_129,c_5668,c_5671,c_5784,c_5781,c_5923,c_6008])).

cnf(c_8867,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8866])).

cnf(c_5282,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8873,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8867,c_5282])).

cnf(c_10172,plain,
    ( v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10162,c_8873])).

cnf(c_5262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7292,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(sK7)))) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7246,c_5262])).

cnf(c_7493,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7292,c_38,c_39,c_125,c_129,c_5669,c_5668,c_5671,c_5765,c_5784,c_5781,c_5923,c_6008])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5278,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7499,plain,
    ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_7493,c_5278])).

cnf(c_10416,plain,
    ( v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_10172,c_7499])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5280,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6265,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5280,c_5278])).

cnf(c_10120,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5282,c_6265])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_5285,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_291,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_292,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_292])).

cnf(c_5260,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_6013,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5282,c_5260])).

cnf(c_6020,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5285,c_6013])).

cnf(c_5283,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6336,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6020,c_5283])).

cnf(c_6734,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6020,c_6336])).

cnf(c_11621,plain,
    ( sK7 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10416,c_6734])).

cnf(c_18172,plain,
    ( k2_zfmisc_1(X0,X1) = sK7
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10120,c_11621])).

cnf(c_36310,plain,
    ( k2_zfmisc_1(X0,sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_10416,c_18172])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_11])).

cnf(c_5259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_5831,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5280,c_5259])).

cnf(c_9779,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5282,c_5831])).

cnf(c_36556,plain,
    ( r1_tarski(k1_relat_1(sK7),X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36310,c_9779])).

cnf(c_36682,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36556,c_7246,c_36310])).

cnf(c_36719,plain,
    ( r1_tarski(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36682,c_38,c_39,c_125,c_129,c_5668,c_5671,c_5784,c_5781,c_5923,c_6008])).

cnf(c_36728,plain,
    ( sK5 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_36719,c_6336])).

cnf(c_36812,plain,
    ( sK5 = sK7
    | v1_xboole_0(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36728])).

cnf(c_4501,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_25135,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_4501])).

cnf(c_25137,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK7)
    | sK5 != sK7 ),
    inference(instantiation,[status(thm)],[c_25135])).

cnf(c_10028,plain,
    ( ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    | r1_tarski(k2_relat_1(sK7),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9981])).

cnf(c_8874,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK6)
    | v1_xboole_0(k2_relat_1(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8873])).

cnf(c_17,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_xboole_0(X1)
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_577])).

cnf(c_624,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_4493,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_xboole_0(sK5)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_624])).

cnf(c_5256,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4493])).

cnf(c_4492,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_624])).

cnf(c_5257,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4492])).

cnf(c_5411,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5256,c_5257])).

cnf(c_7969,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5277,c_5411])).

cnf(c_7976,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7969,c_7246])).

cnf(c_8425,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7976,c_38,c_39,c_125,c_129,c_5669,c_5668,c_5671,c_5765,c_5784,c_5781,c_5923,c_6008])).

cnf(c_8432,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8425,c_5282])).

cnf(c_8433,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK6)
    | ~ v1_xboole_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8432])).

cnf(c_7514,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK7))
    | v1_xboole_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7499])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36812,c_25137,c_10028,c_9981,c_8874,c_8873,c_8433,c_7514,c_7499,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.69/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/1.49  
% 7.69/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.69/1.49  
% 7.69/1.49  ------  iProver source info
% 7.69/1.49  
% 7.69/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.69/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.69/1.49  git: non_committed_changes: false
% 7.69/1.49  git: last_make_outside_of_git: false
% 7.69/1.49  
% 7.69/1.49  ------ 
% 7.69/1.49  
% 7.69/1.49  ------ Input Options
% 7.69/1.49  
% 7.69/1.49  --out_options                           all
% 7.69/1.49  --tptp_safe_out                         true
% 7.69/1.49  --problem_path                          ""
% 7.69/1.49  --include_path                          ""
% 7.69/1.49  --clausifier                            res/vclausify_rel
% 7.69/1.49  --clausifier_options                    --mode clausify
% 7.69/1.49  --stdin                                 false
% 7.69/1.49  --stats_out                             all
% 7.69/1.49  
% 7.69/1.49  ------ General Options
% 7.69/1.49  
% 7.69/1.49  --fof                                   false
% 7.69/1.49  --time_out_real                         305.
% 7.69/1.49  --time_out_virtual                      -1.
% 7.69/1.49  --symbol_type_check                     false
% 7.69/1.49  --clausify_out                          false
% 7.69/1.49  --sig_cnt_out                           false
% 7.69/1.49  --trig_cnt_out                          false
% 7.69/1.49  --trig_cnt_out_tolerance                1.
% 7.69/1.49  --trig_cnt_out_sk_spl                   false
% 7.69/1.49  --abstr_cl_out                          false
% 7.69/1.49  
% 7.69/1.49  ------ Global Options
% 7.69/1.49  
% 7.69/1.49  --schedule                              default
% 7.69/1.49  --add_important_lit                     false
% 7.69/1.49  --prop_solver_per_cl                    1000
% 7.69/1.49  --min_unsat_core                        false
% 7.69/1.49  --soft_assumptions                      false
% 7.69/1.49  --soft_lemma_size                       3
% 7.69/1.49  --prop_impl_unit_size                   0
% 7.69/1.49  --prop_impl_unit                        []
% 7.69/1.49  --share_sel_clauses                     true
% 7.69/1.49  --reset_solvers                         false
% 7.69/1.49  --bc_imp_inh                            [conj_cone]
% 7.69/1.49  --conj_cone_tolerance                   3.
% 7.69/1.49  --extra_neg_conj                        none
% 7.69/1.49  --large_theory_mode                     true
% 7.69/1.49  --prolific_symb_bound                   200
% 7.69/1.49  --lt_threshold                          2000
% 7.69/1.49  --clause_weak_htbl                      true
% 7.69/1.49  --gc_record_bc_elim                     false
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing Options
% 7.69/1.49  
% 7.69/1.49  --preprocessing_flag                    true
% 7.69/1.49  --time_out_prep_mult                    0.1
% 7.69/1.49  --splitting_mode                        input
% 7.69/1.49  --splitting_grd                         true
% 7.69/1.49  --splitting_cvd                         false
% 7.69/1.49  --splitting_cvd_svl                     false
% 7.69/1.49  --splitting_nvd                         32
% 7.69/1.49  --sub_typing                            true
% 7.69/1.49  --prep_gs_sim                           true
% 7.69/1.49  --prep_unflatten                        true
% 7.69/1.49  --prep_res_sim                          true
% 7.69/1.49  --prep_upred                            true
% 7.69/1.49  --prep_sem_filter                       exhaustive
% 7.69/1.49  --prep_sem_filter_out                   false
% 7.69/1.49  --pred_elim                             true
% 7.69/1.49  --res_sim_input                         true
% 7.69/1.49  --eq_ax_congr_red                       true
% 7.69/1.49  --pure_diseq_elim                       true
% 7.69/1.49  --brand_transform                       false
% 7.69/1.49  --non_eq_to_eq                          false
% 7.69/1.49  --prep_def_merge                        true
% 7.69/1.49  --prep_def_merge_prop_impl              false
% 7.69/1.49  --prep_def_merge_mbd                    true
% 7.69/1.49  --prep_def_merge_tr_red                 false
% 7.69/1.49  --prep_def_merge_tr_cl                  false
% 7.69/1.49  --smt_preprocessing                     true
% 7.69/1.49  --smt_ac_axioms                         fast
% 7.69/1.49  --preprocessed_out                      false
% 7.69/1.49  --preprocessed_stats                    false
% 7.69/1.49  
% 7.69/1.49  ------ Abstraction refinement Options
% 7.69/1.49  
% 7.69/1.49  --abstr_ref                             []
% 7.69/1.49  --abstr_ref_prep                        false
% 7.69/1.49  --abstr_ref_until_sat                   false
% 7.69/1.49  --abstr_ref_sig_restrict                funpre
% 7.69/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.49  --abstr_ref_under                       []
% 7.69/1.49  
% 7.69/1.49  ------ SAT Options
% 7.69/1.49  
% 7.69/1.49  --sat_mode                              false
% 7.69/1.49  --sat_fm_restart_options                ""
% 7.69/1.49  --sat_gr_def                            false
% 7.69/1.49  --sat_epr_types                         true
% 7.69/1.49  --sat_non_cyclic_types                  false
% 7.69/1.49  --sat_finite_models                     false
% 7.69/1.49  --sat_fm_lemmas                         false
% 7.69/1.49  --sat_fm_prep                           false
% 7.69/1.49  --sat_fm_uc_incr                        true
% 7.69/1.49  --sat_out_model                         small
% 7.69/1.49  --sat_out_clauses                       false
% 7.69/1.49  
% 7.69/1.49  ------ QBF Options
% 7.69/1.49  
% 7.69/1.49  --qbf_mode                              false
% 7.69/1.49  --qbf_elim_univ                         false
% 7.69/1.49  --qbf_dom_inst                          none
% 7.69/1.49  --qbf_dom_pre_inst                      false
% 7.69/1.49  --qbf_sk_in                             false
% 7.69/1.49  --qbf_pred_elim                         true
% 7.69/1.49  --qbf_split                             512
% 7.69/1.49  
% 7.69/1.49  ------ BMC1 Options
% 7.69/1.49  
% 7.69/1.49  --bmc1_incremental                      false
% 7.69/1.49  --bmc1_axioms                           reachable_all
% 7.69/1.49  --bmc1_min_bound                        0
% 7.69/1.49  --bmc1_max_bound                        -1
% 7.69/1.49  --bmc1_max_bound_default                -1
% 7.69/1.49  --bmc1_symbol_reachability              true
% 7.69/1.49  --bmc1_property_lemmas                  false
% 7.69/1.49  --bmc1_k_induction                      false
% 7.69/1.49  --bmc1_non_equiv_states                 false
% 7.69/1.49  --bmc1_deadlock                         false
% 7.69/1.49  --bmc1_ucm                              false
% 7.69/1.49  --bmc1_add_unsat_core                   none
% 7.69/1.49  --bmc1_unsat_core_children              false
% 7.69/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.49  --bmc1_out_stat                         full
% 7.69/1.49  --bmc1_ground_init                      false
% 7.69/1.49  --bmc1_pre_inst_next_state              false
% 7.69/1.49  --bmc1_pre_inst_state                   false
% 7.69/1.49  --bmc1_pre_inst_reach_state             false
% 7.69/1.49  --bmc1_out_unsat_core                   false
% 7.69/1.49  --bmc1_aig_witness_out                  false
% 7.69/1.49  --bmc1_verbose                          false
% 7.69/1.49  --bmc1_dump_clauses_tptp                false
% 7.69/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.49  --bmc1_dump_file                        -
% 7.69/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.49  --bmc1_ucm_extend_mode                  1
% 7.69/1.49  --bmc1_ucm_init_mode                    2
% 7.69/1.49  --bmc1_ucm_cone_mode                    none
% 7.69/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.49  --bmc1_ucm_relax_model                  4
% 7.69/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.49  --bmc1_ucm_layered_model                none
% 7.69/1.49  --bmc1_ucm_max_lemma_size               10
% 7.69/1.49  
% 7.69/1.49  ------ AIG Options
% 7.69/1.49  
% 7.69/1.49  --aig_mode                              false
% 7.69/1.49  
% 7.69/1.49  ------ Instantiation Options
% 7.69/1.49  
% 7.69/1.49  --instantiation_flag                    true
% 7.69/1.49  --inst_sos_flag                         false
% 7.69/1.49  --inst_sos_phase                        true
% 7.69/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.49  --inst_lit_sel_side                     num_symb
% 7.69/1.49  --inst_solver_per_active                1400
% 7.69/1.49  --inst_solver_calls_frac                1.
% 7.69/1.49  --inst_passive_queue_type               priority_queues
% 7.69/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.49  --inst_passive_queues_freq              [25;2]
% 7.69/1.49  --inst_dismatching                      true
% 7.69/1.49  --inst_eager_unprocessed_to_passive     true
% 7.69/1.49  --inst_prop_sim_given                   true
% 7.69/1.49  --inst_prop_sim_new                     false
% 7.69/1.49  --inst_subs_new                         false
% 7.69/1.49  --inst_eq_res_simp                      false
% 7.69/1.49  --inst_subs_given                       false
% 7.69/1.49  --inst_orphan_elimination               true
% 7.69/1.49  --inst_learning_loop_flag               true
% 7.69/1.49  --inst_learning_start                   3000
% 7.69/1.49  --inst_learning_factor                  2
% 7.69/1.49  --inst_start_prop_sim_after_learn       3
% 7.69/1.49  --inst_sel_renew                        solver
% 7.69/1.49  --inst_lit_activity_flag                true
% 7.69/1.49  --inst_restr_to_given                   false
% 7.69/1.49  --inst_activity_threshold               500
% 7.69/1.49  --inst_out_proof                        true
% 7.69/1.49  
% 7.69/1.49  ------ Resolution Options
% 7.69/1.49  
% 7.69/1.49  --resolution_flag                       true
% 7.69/1.49  --res_lit_sel                           adaptive
% 7.69/1.49  --res_lit_sel_side                      none
% 7.69/1.49  --res_ordering                          kbo
% 7.69/1.49  --res_to_prop_solver                    active
% 7.69/1.49  --res_prop_simpl_new                    false
% 7.69/1.49  --res_prop_simpl_given                  true
% 7.69/1.49  --res_passive_queue_type                priority_queues
% 7.69/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.49  --res_passive_queues_freq               [15;5]
% 7.69/1.49  --res_forward_subs                      full
% 7.69/1.49  --res_backward_subs                     full
% 7.69/1.49  --res_forward_subs_resolution           true
% 7.69/1.49  --res_backward_subs_resolution          true
% 7.69/1.49  --res_orphan_elimination                true
% 7.69/1.49  --res_time_limit                        2.
% 7.69/1.49  --res_out_proof                         true
% 7.69/1.49  
% 7.69/1.49  ------ Superposition Options
% 7.69/1.49  
% 7.69/1.49  --superposition_flag                    true
% 7.69/1.49  --sup_passive_queue_type                priority_queues
% 7.69/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.69/1.49  --demod_completeness_check              fast
% 7.69/1.49  --demod_use_ground                      true
% 7.69/1.49  --sup_to_prop_solver                    passive
% 7.69/1.49  --sup_prop_simpl_new                    true
% 7.69/1.49  --sup_prop_simpl_given                  true
% 7.69/1.49  --sup_fun_splitting                     false
% 7.69/1.49  --sup_smt_interval                      50000
% 7.69/1.49  
% 7.69/1.49  ------ Superposition Simplification Setup
% 7.69/1.49  
% 7.69/1.49  --sup_indices_passive                   []
% 7.69/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.49  --sup_full_bw                           [BwDemod]
% 7.69/1.49  --sup_immed_triv                        [TrivRules]
% 7.69/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.49  --sup_immed_bw_main                     []
% 7.69/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.49  
% 7.69/1.49  ------ Combination Options
% 7.69/1.49  
% 7.69/1.49  --comb_res_mult                         3
% 7.69/1.49  --comb_sup_mult                         2
% 7.69/1.49  --comb_inst_mult                        10
% 7.69/1.49  
% 7.69/1.49  ------ Debug Options
% 7.69/1.49  
% 7.69/1.49  --dbg_backtrace                         false
% 7.69/1.49  --dbg_dump_prop_clauses                 false
% 7.69/1.49  --dbg_dump_prop_clauses_file            -
% 7.69/1.49  --dbg_out_stat                          false
% 7.69/1.49  ------ Parsing...
% 7.69/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.69/1.49  ------ Proving...
% 7.69/1.49  ------ Problem Properties 
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  clauses                                 32
% 7.69/1.49  conjectures                             1
% 7.69/1.49  EPR                                     5
% 7.69/1.49  Horn                                    26
% 7.69/1.49  unary                                   3
% 7.69/1.49  binary                                  6
% 7.69/1.49  lits                                    95
% 7.69/1.49  lits eq                                 10
% 7.69/1.49  fd_pure                                 0
% 7.69/1.49  fd_pseudo                               0
% 7.69/1.49  fd_cond                                 0
% 7.69/1.49  fd_pseudo_cond                          2
% 7.69/1.49  AC symbols                              0
% 7.69/1.49  
% 7.69/1.49  ------ Schedule dynamic 5 is on 
% 7.69/1.49  
% 7.69/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  ------ 
% 7.69/1.49  Current options:
% 7.69/1.49  ------ 
% 7.69/1.49  
% 7.69/1.49  ------ Input Options
% 7.69/1.49  
% 7.69/1.49  --out_options                           all
% 7.69/1.49  --tptp_safe_out                         true
% 7.69/1.49  --problem_path                          ""
% 7.69/1.49  --include_path                          ""
% 7.69/1.49  --clausifier                            res/vclausify_rel
% 7.69/1.49  --clausifier_options                    --mode clausify
% 7.69/1.49  --stdin                                 false
% 7.69/1.49  --stats_out                             all
% 7.69/1.49  
% 7.69/1.49  ------ General Options
% 7.69/1.49  
% 7.69/1.49  --fof                                   false
% 7.69/1.49  --time_out_real                         305.
% 7.69/1.49  --time_out_virtual                      -1.
% 7.69/1.49  --symbol_type_check                     false
% 7.69/1.49  --clausify_out                          false
% 7.69/1.49  --sig_cnt_out                           false
% 7.69/1.49  --trig_cnt_out                          false
% 7.69/1.49  --trig_cnt_out_tolerance                1.
% 7.69/1.49  --trig_cnt_out_sk_spl                   false
% 7.69/1.49  --abstr_cl_out                          false
% 7.69/1.49  
% 7.69/1.49  ------ Global Options
% 7.69/1.49  
% 7.69/1.49  --schedule                              default
% 7.69/1.49  --add_important_lit                     false
% 7.69/1.49  --prop_solver_per_cl                    1000
% 7.69/1.49  --min_unsat_core                        false
% 7.69/1.49  --soft_assumptions                      false
% 7.69/1.49  --soft_lemma_size                       3
% 7.69/1.49  --prop_impl_unit_size                   0
% 7.69/1.49  --prop_impl_unit                        []
% 7.69/1.49  --share_sel_clauses                     true
% 7.69/1.49  --reset_solvers                         false
% 7.69/1.49  --bc_imp_inh                            [conj_cone]
% 7.69/1.49  --conj_cone_tolerance                   3.
% 7.69/1.49  --extra_neg_conj                        none
% 7.69/1.49  --large_theory_mode                     true
% 7.69/1.49  --prolific_symb_bound                   200
% 7.69/1.49  --lt_threshold                          2000
% 7.69/1.49  --clause_weak_htbl                      true
% 7.69/1.49  --gc_record_bc_elim                     false
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing Options
% 7.69/1.49  
% 7.69/1.49  --preprocessing_flag                    true
% 7.69/1.49  --time_out_prep_mult                    0.1
% 7.69/1.49  --splitting_mode                        input
% 7.69/1.49  --splitting_grd                         true
% 7.69/1.49  --splitting_cvd                         false
% 7.69/1.49  --splitting_cvd_svl                     false
% 7.69/1.49  --splitting_nvd                         32
% 7.69/1.49  --sub_typing                            true
% 7.69/1.49  --prep_gs_sim                           true
% 7.69/1.49  --prep_unflatten                        true
% 7.69/1.49  --prep_res_sim                          true
% 7.69/1.49  --prep_upred                            true
% 7.69/1.49  --prep_sem_filter                       exhaustive
% 7.69/1.49  --prep_sem_filter_out                   false
% 7.69/1.49  --pred_elim                             true
% 7.69/1.49  --res_sim_input                         true
% 7.69/1.49  --eq_ax_congr_red                       true
% 7.69/1.49  --pure_diseq_elim                       true
% 7.69/1.49  --brand_transform                       false
% 7.69/1.49  --non_eq_to_eq                          false
% 7.69/1.49  --prep_def_merge                        true
% 7.69/1.49  --prep_def_merge_prop_impl              false
% 7.69/1.49  --prep_def_merge_mbd                    true
% 7.69/1.49  --prep_def_merge_tr_red                 false
% 7.69/1.49  --prep_def_merge_tr_cl                  false
% 7.69/1.49  --smt_preprocessing                     true
% 7.69/1.49  --smt_ac_axioms                         fast
% 7.69/1.49  --preprocessed_out                      false
% 7.69/1.49  --preprocessed_stats                    false
% 7.69/1.49  
% 7.69/1.49  ------ Abstraction refinement Options
% 7.69/1.49  
% 7.69/1.49  --abstr_ref                             []
% 7.69/1.49  --abstr_ref_prep                        false
% 7.69/1.49  --abstr_ref_until_sat                   false
% 7.69/1.49  --abstr_ref_sig_restrict                funpre
% 7.69/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.49  --abstr_ref_under                       []
% 7.69/1.49  
% 7.69/1.49  ------ SAT Options
% 7.69/1.49  
% 7.69/1.49  --sat_mode                              false
% 7.69/1.49  --sat_fm_restart_options                ""
% 7.69/1.49  --sat_gr_def                            false
% 7.69/1.49  --sat_epr_types                         true
% 7.69/1.49  --sat_non_cyclic_types                  false
% 7.69/1.49  --sat_finite_models                     false
% 7.69/1.49  --sat_fm_lemmas                         false
% 7.69/1.49  --sat_fm_prep                           false
% 7.69/1.49  --sat_fm_uc_incr                        true
% 7.69/1.49  --sat_out_model                         small
% 7.69/1.49  --sat_out_clauses                       false
% 7.69/1.49  
% 7.69/1.49  ------ QBF Options
% 7.69/1.49  
% 7.69/1.49  --qbf_mode                              false
% 7.69/1.49  --qbf_elim_univ                         false
% 7.69/1.49  --qbf_dom_inst                          none
% 7.69/1.49  --qbf_dom_pre_inst                      false
% 7.69/1.49  --qbf_sk_in                             false
% 7.69/1.49  --qbf_pred_elim                         true
% 7.69/1.49  --qbf_split                             512
% 7.69/1.49  
% 7.69/1.49  ------ BMC1 Options
% 7.69/1.49  
% 7.69/1.49  --bmc1_incremental                      false
% 7.69/1.49  --bmc1_axioms                           reachable_all
% 7.69/1.49  --bmc1_min_bound                        0
% 7.69/1.49  --bmc1_max_bound                        -1
% 7.69/1.49  --bmc1_max_bound_default                -1
% 7.69/1.49  --bmc1_symbol_reachability              true
% 7.69/1.49  --bmc1_property_lemmas                  false
% 7.69/1.49  --bmc1_k_induction                      false
% 7.69/1.49  --bmc1_non_equiv_states                 false
% 7.69/1.49  --bmc1_deadlock                         false
% 7.69/1.49  --bmc1_ucm                              false
% 7.69/1.49  --bmc1_add_unsat_core                   none
% 7.69/1.49  --bmc1_unsat_core_children              false
% 7.69/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.49  --bmc1_out_stat                         full
% 7.69/1.49  --bmc1_ground_init                      false
% 7.69/1.49  --bmc1_pre_inst_next_state              false
% 7.69/1.49  --bmc1_pre_inst_state                   false
% 7.69/1.49  --bmc1_pre_inst_reach_state             false
% 7.69/1.49  --bmc1_out_unsat_core                   false
% 7.69/1.49  --bmc1_aig_witness_out                  false
% 7.69/1.49  --bmc1_verbose                          false
% 7.69/1.49  --bmc1_dump_clauses_tptp                false
% 7.69/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.49  --bmc1_dump_file                        -
% 7.69/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.49  --bmc1_ucm_extend_mode                  1
% 7.69/1.49  --bmc1_ucm_init_mode                    2
% 7.69/1.49  --bmc1_ucm_cone_mode                    none
% 7.69/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.49  --bmc1_ucm_relax_model                  4
% 7.69/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.49  --bmc1_ucm_layered_model                none
% 7.69/1.49  --bmc1_ucm_max_lemma_size               10
% 7.69/1.49  
% 7.69/1.49  ------ AIG Options
% 7.69/1.49  
% 7.69/1.49  --aig_mode                              false
% 7.69/1.49  
% 7.69/1.49  ------ Instantiation Options
% 7.69/1.49  
% 7.69/1.49  --instantiation_flag                    true
% 7.69/1.49  --inst_sos_flag                         false
% 7.69/1.49  --inst_sos_phase                        true
% 7.69/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.49  --inst_lit_sel_side                     none
% 7.69/1.49  --inst_solver_per_active                1400
% 7.69/1.49  --inst_solver_calls_frac                1.
% 7.69/1.49  --inst_passive_queue_type               priority_queues
% 7.69/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.49  --inst_passive_queues_freq              [25;2]
% 7.69/1.49  --inst_dismatching                      true
% 7.69/1.49  --inst_eager_unprocessed_to_passive     true
% 7.69/1.49  --inst_prop_sim_given                   true
% 7.69/1.49  --inst_prop_sim_new                     false
% 7.69/1.49  --inst_subs_new                         false
% 7.69/1.49  --inst_eq_res_simp                      false
% 7.69/1.49  --inst_subs_given                       false
% 7.69/1.49  --inst_orphan_elimination               true
% 7.69/1.49  --inst_learning_loop_flag               true
% 7.69/1.49  --inst_learning_start                   3000
% 7.69/1.49  --inst_learning_factor                  2
% 7.69/1.49  --inst_start_prop_sim_after_learn       3
% 7.69/1.49  --inst_sel_renew                        solver
% 7.69/1.49  --inst_lit_activity_flag                true
% 7.69/1.49  --inst_restr_to_given                   false
% 7.69/1.49  --inst_activity_threshold               500
% 7.69/1.49  --inst_out_proof                        true
% 7.69/1.49  
% 7.69/1.49  ------ Resolution Options
% 7.69/1.49  
% 7.69/1.49  --resolution_flag                       false
% 7.69/1.49  --res_lit_sel                           adaptive
% 7.69/1.49  --res_lit_sel_side                      none
% 7.69/1.49  --res_ordering                          kbo
% 7.69/1.49  --res_to_prop_solver                    active
% 7.69/1.49  --res_prop_simpl_new                    false
% 7.69/1.49  --res_prop_simpl_given                  true
% 7.69/1.49  --res_passive_queue_type                priority_queues
% 7.69/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.49  --res_passive_queues_freq               [15;5]
% 7.69/1.49  --res_forward_subs                      full
% 7.69/1.49  --res_backward_subs                     full
% 7.69/1.49  --res_forward_subs_resolution           true
% 7.69/1.49  --res_backward_subs_resolution          true
% 7.69/1.49  --res_orphan_elimination                true
% 7.69/1.49  --res_time_limit                        2.
% 7.69/1.49  --res_out_proof                         true
% 7.69/1.49  
% 7.69/1.49  ------ Superposition Options
% 7.69/1.49  
% 7.69/1.49  --superposition_flag                    true
% 7.69/1.49  --sup_passive_queue_type                priority_queues
% 7.69/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.69/1.49  --demod_completeness_check              fast
% 7.69/1.49  --demod_use_ground                      true
% 7.69/1.49  --sup_to_prop_solver                    passive
% 7.69/1.49  --sup_prop_simpl_new                    true
% 7.69/1.49  --sup_prop_simpl_given                  true
% 7.69/1.49  --sup_fun_splitting                     false
% 7.69/1.49  --sup_smt_interval                      50000
% 7.69/1.49  
% 7.69/1.49  ------ Superposition Simplification Setup
% 7.69/1.49  
% 7.69/1.49  --sup_indices_passive                   []
% 7.69/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.49  --sup_full_bw                           [BwDemod]
% 7.69/1.49  --sup_immed_triv                        [TrivRules]
% 7.69/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.49  --sup_immed_bw_main                     []
% 7.69/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.49  
% 7.69/1.49  ------ Combination Options
% 7.69/1.49  
% 7.69/1.49  --comb_res_mult                         3
% 7.69/1.49  --comb_sup_mult                         2
% 7.69/1.49  --comb_inst_mult                        10
% 7.69/1.49  
% 7.69/1.49  ------ Debug Options
% 7.69/1.49  
% 7.69/1.49  --dbg_backtrace                         false
% 7.69/1.49  --dbg_dump_prop_clauses                 false
% 7.69/1.49  --dbg_dump_prop_clauses_file            -
% 7.69/1.49  --dbg_out_stat                          false
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  ------ Proving...
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  % SZS status Theorem for theBenchmark.p
% 7.69/1.49  
% 7.69/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.69/1.49  
% 7.69/1.49  fof(f15,conjecture,(
% 7.69/1.49    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f16,negated_conjecture,(
% 7.69/1.49    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.69/1.49    inference(negated_conjecture,[],[f15])).
% 7.69/1.49  
% 7.69/1.49  fof(f34,plain,(
% 7.69/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 7.69/1.49    inference(ennf_transformation,[],[f16])).
% 7.69/1.49  
% 7.69/1.49  fof(f52,plain,(
% 7.69/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7)) & r2_hidden(sK7,k1_funct_2(sK5,sK6)))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f53,plain,(
% 7.69/1.49    (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7)) & r2_hidden(sK7,k1_funct_2(sK5,sK6))),
% 7.69/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f34,f52])).
% 7.69/1.49  
% 7.69/1.49  fof(f91,plain,(
% 7.69/1.49    r2_hidden(sK7,k1_funct_2(sK5,sK6))),
% 7.69/1.49    inference(cnf_transformation,[],[f53])).
% 7.69/1.49  
% 7.69/1.49  fof(f13,axiom,(
% 7.69/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f35,plain,(
% 7.69/1.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.69/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.69/1.49  
% 7.69/1.49  fof(f36,plain,(
% 7.69/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 7.69/1.49    inference(definition_folding,[],[f13,f35])).
% 7.69/1.49  
% 7.69/1.49  fof(f51,plain,(
% 7.69/1.49    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 7.69/1.49    inference(nnf_transformation,[],[f36])).
% 7.69/1.49  
% 7.69/1.49  fof(f86,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 7.69/1.49    inference(cnf_transformation,[],[f51])).
% 7.69/1.49  
% 7.69/1.49  fof(f98,plain,(
% 7.69/1.49    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 7.69/1.49    inference(equality_resolution,[],[f86])).
% 7.69/1.49  
% 7.69/1.49  fof(f45,plain,(
% 7.69/1.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 7.69/1.49    inference(nnf_transformation,[],[f35])).
% 7.69/1.49  
% 7.69/1.49  fof(f46,plain,(
% 7.69/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.69/1.49    inference(rectify,[],[f45])).
% 7.69/1.49  
% 7.69/1.49  fof(f49,plain,(
% 7.69/1.49    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) & k1_relat_1(sK4(X0,X1,X6)) = X1 & sK4(X0,X1,X6) = X6 & v1_funct_1(sK4(X0,X1,X6)) & v1_relat_1(sK4(X0,X1,X6))))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f48,plain,(
% 7.69/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0) & k1_relat_1(sK3(X0,X1,X2)) = X1 & sK3(X0,X1,X2) = X3 & v1_funct_1(sK3(X0,X1,X2)) & v1_relat_1(sK3(X0,X1,X2))))) )),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f47,plain,(
% 7.69/1.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK2(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK2(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f50,plain,(
% 7.69/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK2(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0) & k1_relat_1(sK3(X0,X1,X2)) = X1 & sK2(X0,X1,X2) = sK3(X0,X1,X2) & v1_funct_1(sK3(X0,X1,X2)) & v1_relat_1(sK3(X0,X1,X2))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) & k1_relat_1(sK4(X0,X1,X6)) = X1 & sK4(X0,X1,X6) = X6 & v1_funct_1(sK4(X0,X1,X6)) & v1_relat_1(sK4(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.69/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f46,f49,f48,f47])).
% 7.69/1.49  
% 7.69/1.49  fof(f76,plain,(
% 7.69/1.49    ( ! [X6,X2,X0,X1] : (sK4(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f50])).
% 7.69/1.49  
% 7.69/1.49  fof(f78,plain,(
% 7.69/1.49    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f50])).
% 7.69/1.49  
% 7.69/1.49  fof(f9,axiom,(
% 7.69/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f25,plain,(
% 7.69/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.69/1.49    inference(ennf_transformation,[],[f9])).
% 7.69/1.49  
% 7.69/1.49  fof(f26,plain,(
% 7.69/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.69/1.49    inference(flattening,[],[f25])).
% 7.69/1.49  
% 7.69/1.49  fof(f68,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f26])).
% 7.69/1.49  
% 7.69/1.49  fof(f77,plain,(
% 7.69/1.49    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK4(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f50])).
% 7.69/1.49  
% 7.69/1.49  fof(f12,axiom,(
% 7.69/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f30,plain,(
% 7.69/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.69/1.49    inference(ennf_transformation,[],[f12])).
% 7.69/1.49  
% 7.69/1.49  fof(f31,plain,(
% 7.69/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.69/1.49    inference(flattening,[],[f30])).
% 7.69/1.49  
% 7.69/1.49  fof(f73,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f31])).
% 7.69/1.49  
% 7.69/1.49  fof(f14,axiom,(
% 7.69/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f32,plain,(
% 7.69/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.69/1.49    inference(ennf_transformation,[],[f14])).
% 7.69/1.49  
% 7.69/1.49  fof(f33,plain,(
% 7.69/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.69/1.49    inference(flattening,[],[f32])).
% 7.69/1.49  
% 7.69/1.49  fof(f89,plain,(
% 7.69/1.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f33])).
% 7.69/1.49  
% 7.69/1.49  fof(f90,plain,(
% 7.69/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f33])).
% 7.69/1.49  
% 7.69/1.49  fof(f10,axiom,(
% 7.69/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f27,plain,(
% 7.69/1.49    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.49    inference(ennf_transformation,[],[f10])).
% 7.69/1.49  
% 7.69/1.49  fof(f28,plain,(
% 7.69/1.49    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.49    inference(flattening,[],[f27])).
% 7.69/1.49  
% 7.69/1.49  fof(f70,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.49    inference(cnf_transformation,[],[f28])).
% 7.69/1.49  
% 7.69/1.49  fof(f92,plain,(
% 7.69/1.49    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7)),
% 7.69/1.49    inference(cnf_transformation,[],[f53])).
% 7.69/1.49  
% 7.69/1.49  fof(f2,axiom,(
% 7.69/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f41,plain,(
% 7.69/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.69/1.49    inference(nnf_transformation,[],[f2])).
% 7.69/1.49  
% 7.69/1.49  fof(f42,plain,(
% 7.69/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.69/1.49    inference(flattening,[],[f41])).
% 7.69/1.49  
% 7.69/1.49  fof(f57,plain,(
% 7.69/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.69/1.49    inference(cnf_transformation,[],[f42])).
% 7.69/1.49  
% 7.69/1.49  fof(f94,plain,(
% 7.69/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.69/1.49    inference(equality_resolution,[],[f57])).
% 7.69/1.49  
% 7.69/1.49  fof(f59,plain,(
% 7.69/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f42])).
% 7.69/1.49  
% 7.69/1.49  fof(f75,plain,(
% 7.69/1.49    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK4(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f50])).
% 7.69/1.49  
% 7.69/1.49  fof(f74,plain,(
% 7.69/1.49    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK4(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f50])).
% 7.69/1.49  
% 7.69/1.49  fof(f8,axiom,(
% 7.69/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f24,plain,(
% 7.69/1.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.69/1.49    inference(ennf_transformation,[],[f8])).
% 7.69/1.49  
% 7.69/1.49  fof(f67,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f24])).
% 7.69/1.49  
% 7.69/1.49  fof(f4,axiom,(
% 7.69/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f43,plain,(
% 7.69/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.69/1.49    inference(nnf_transformation,[],[f4])).
% 7.69/1.49  
% 7.69/1.49  fof(f62,plain,(
% 7.69/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f43])).
% 7.69/1.49  
% 7.69/1.49  fof(f1,axiom,(
% 7.69/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f18,plain,(
% 7.69/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.69/1.49    inference(ennf_transformation,[],[f1])).
% 7.69/1.49  
% 7.69/1.49  fof(f37,plain,(
% 7.69/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.69/1.49    inference(nnf_transformation,[],[f18])).
% 7.69/1.49  
% 7.69/1.49  fof(f38,plain,(
% 7.69/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.69/1.49    inference(rectify,[],[f37])).
% 7.69/1.49  
% 7.69/1.49  fof(f39,plain,(
% 7.69/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.69/1.49    introduced(choice_axiom,[])).
% 7.69/1.49  
% 7.69/1.49  fof(f40,plain,(
% 7.69/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.69/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 7.69/1.49  
% 7.69/1.49  fof(f55,plain,(
% 7.69/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f40])).
% 7.69/1.49  
% 7.69/1.49  fof(f5,axiom,(
% 7.69/1.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f21,plain,(
% 7.69/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.69/1.49    inference(ennf_transformation,[],[f5])).
% 7.69/1.49  
% 7.69/1.49  fof(f63,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f21])).
% 7.69/1.49  
% 7.69/1.49  fof(f7,axiom,(
% 7.69/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f17,plain,(
% 7.69/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.69/1.49    inference(pure_predicate_removal,[],[f7])).
% 7.69/1.49  
% 7.69/1.49  fof(f23,plain,(
% 7.69/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.69/1.49    inference(ennf_transformation,[],[f17])).
% 7.69/1.49  
% 7.69/1.49  fof(f66,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.69/1.49    inference(cnf_transformation,[],[f23])).
% 7.69/1.49  
% 7.69/1.49  fof(f6,axiom,(
% 7.69/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f22,plain,(
% 7.69/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.69/1.49    inference(ennf_transformation,[],[f6])).
% 7.69/1.49  
% 7.69/1.49  fof(f44,plain,(
% 7.69/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.69/1.49    inference(nnf_transformation,[],[f22])).
% 7.69/1.49  
% 7.69/1.49  fof(f64,plain,(
% 7.69/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f44])).
% 7.69/1.49  
% 7.69/1.49  fof(f11,axiom,(
% 7.69/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 7.69/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.69/1.49  
% 7.69/1.49  fof(f29,plain,(
% 7.69/1.49    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.69/1.49    inference(ennf_transformation,[],[f11])).
% 7.69/1.49  
% 7.69/1.49  fof(f71,plain,(
% 7.69/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.69/1.49    inference(cnf_transformation,[],[f29])).
% 7.69/1.49  
% 7.69/1.49  cnf(c_38,negated_conjecture,
% 7.69/1.49      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
% 7.69/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5261,plain,
% 7.69/1.49      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_33,plain,
% 7.69/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 7.69/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5263,plain,
% 7.69/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_29,plain,
% 7.69/1.49      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK4(X0,X1,X3) = X3 ),
% 7.69/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5267,plain,
% 7.69/1.49      ( sK4(X0,X1,X2) = X2
% 7.69/1.49      | sP0(X0,X1,X3) != iProver_top
% 7.69/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6289,plain,
% 7.69/1.49      ( sK4(X0,X1,X2) = X2
% 7.69/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5263,c_5267]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6557,plain,
% 7.69/1.49      ( sK4(sK6,sK5,sK7) = sK7 ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5261,c_6289]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_27,plain,
% 7.69/1.49      ( ~ sP0(X0,X1,X2)
% 7.69/1.49      | ~ r2_hidden(X3,X2)
% 7.69/1.49      | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5269,plain,
% 7.69/1.49      ( sP0(X0,X1,X2) != iProver_top
% 7.69/1.49      | r2_hidden(X3,X2) != iProver_top
% 7.69/1.49      | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7520,plain,
% 7.69/1.49      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 7.69/1.49      | r1_tarski(k2_relat_1(sK4(X2,X1,X0)),X2) = iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5263,c_5269]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_9981,plain,
% 7.69/1.49      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
% 7.69/1.49      | r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_6557,c_7520]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_39,plain,
% 7.69/1.49      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_10162,plain,
% 7.69/1.49      ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_9981,c_39]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_14,plain,
% 7.69/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.69/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.69/1.49      | ~ v1_relat_1(X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5277,plain,
% 7.69/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.69/1.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.69/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.69/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_28,plain,
% 7.69/1.49      ( ~ sP0(X0,X1,X2)
% 7.69/1.49      | ~ r2_hidden(X3,X2)
% 7.69/1.49      | k1_relat_1(sK4(X0,X1,X3)) = X1 ),
% 7.69/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5268,plain,
% 7.69/1.49      ( k1_relat_1(sK4(X0,X1,X2)) = X1
% 7.69/1.49      | sP0(X0,X1,X3) != iProver_top
% 7.69/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6855,plain,
% 7.69/1.49      ( k1_relat_1(sK4(X0,X1,X2)) = X1
% 7.69/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5263,c_5268]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7244,plain,
% 7.69/1.49      ( k1_relat_1(sK4(sK6,sK5,sK7)) = sK5 ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5261,c_6855]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7246,plain,
% 7.69/1.49      ( k1_relat_1(sK7) = sK5 ),
% 7.69/1.49      inference(light_normalisation,[status(thm)],[c_7244,c_6557]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_18,plain,
% 7.69/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.69/1.49      | v1_partfun1(X0,X1)
% 7.69/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.49      | ~ v1_funct_1(X0)
% 7.69/1.49      | v1_xboole_0(X2) ),
% 7.69/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_35,plain,
% 7.69/1.49      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.69/1.49      | ~ v1_funct_1(X0)
% 7.69/1.49      | ~ v1_relat_1(X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_552,plain,
% 7.69/1.49      ( v1_partfun1(X0,X1)
% 7.69/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.49      | ~ v1_funct_1(X3)
% 7.69/1.49      | ~ v1_funct_1(X0)
% 7.69/1.49      | ~ v1_relat_1(X3)
% 7.69/1.49      | v1_xboole_0(X2)
% 7.69/1.49      | X3 != X0
% 7.69/1.49      | k2_relat_1(X3) != X2
% 7.69/1.49      | k1_relat_1(X3) != X1 ),
% 7.69/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_553,plain,
% 7.69/1.49      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.69/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.69/1.49      | ~ v1_funct_1(X0)
% 7.69/1.49      | ~ v1_relat_1(X0)
% 7.69/1.49      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.69/1.49      inference(unflattening,[status(thm)],[c_552]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_34,plain,
% 7.69/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.69/1.49      | ~ v1_funct_1(X0)
% 7.69/1.49      | ~ v1_relat_1(X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_557,plain,
% 7.69/1.49      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.69/1.49      | ~ v1_funct_1(X0)
% 7.69/1.49      | ~ v1_relat_1(X0)
% 7.69/1.49      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_553,c_34]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_15,plain,
% 7.69/1.49      ( v1_funct_2(X0,X1,X2)
% 7.69/1.49      | ~ v1_partfun1(X0,X1)
% 7.69/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.49      | ~ v1_funct_1(X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_37,negated_conjecture,
% 7.69/1.49      ( ~ v1_funct_2(sK7,sK5,sK6)
% 7.69/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.69/1.49      | ~ v1_funct_1(sK7) ),
% 7.69/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_576,plain,
% 7.69/1.49      ( ~ v1_partfun1(X0,X1)
% 7.69/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.69/1.49      | ~ v1_funct_1(X0)
% 7.69/1.49      | ~ v1_funct_1(sK7)
% 7.69/1.49      | sK6 != X2
% 7.69/1.49      | sK5 != X1
% 7.69/1.49      | sK7 != X0 ),
% 7.69/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_37]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_577,plain,
% 7.69/1.49      ( ~ v1_partfun1(sK7,sK5)
% 7.69/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.69/1.49      | ~ v1_funct_1(sK7) ),
% 7.69/1.49      inference(unflattening,[status(thm)],[c_576]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_641,plain,
% 7.69/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.69/1.49      | ~ v1_funct_1(X0)
% 7.69/1.49      | ~ v1_funct_1(sK7)
% 7.69/1.49      | ~ v1_relat_1(X0)
% 7.69/1.49      | v1_xboole_0(k2_relat_1(X0))
% 7.69/1.49      | k1_relat_1(X0) != sK5
% 7.69/1.49      | sK7 != X0 ),
% 7.69/1.49      inference(resolution_lifted,[status(thm)],[c_557,c_577]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_642,plain,
% 7.69/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.69/1.49      | ~ v1_funct_1(sK7)
% 7.69/1.49      | ~ v1_relat_1(sK7)
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7))
% 7.69/1.49      | k1_relat_1(sK7) != sK5 ),
% 7.69/1.49      inference(unflattening,[status(thm)],[c_641]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5255,plain,
% 7.69/1.49      ( k1_relat_1(sK7) != sK5
% 7.69/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.69/1.49      | v1_funct_1(sK7) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7270,plain,
% 7.69/1.49      ( sK5 != sK5
% 7.69/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.69/1.49      | v1_funct_1(sK7) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(demodulation,[status(thm)],[c_7246,c_5255]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7281,plain,
% 7.69/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.69/1.49      | v1_funct_1(sK7) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(equality_resolution_simp,[status(thm)],[c_7270]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5,plain,
% 7.69/1.49      ( r1_tarski(X0,X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_125,plain,
% 7.69/1.49      ( r1_tarski(sK7,sK7) ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_3,plain,
% 7.69/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.69/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_129,plain,
% 7.69/1.49      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_643,plain,
% 7.69/1.49      ( k1_relat_1(sK7) != sK5
% 7.69/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.69/1.49      | v1_funct_1(sK7) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_30,plain,
% 7.69/1.49      ( ~ sP0(X0,X1,X2)
% 7.69/1.49      | ~ r2_hidden(X3,X2)
% 7.69/1.49      | v1_funct_1(sK4(X0,X1,X3)) ),
% 7.69/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5561,plain,
% 7.69/1.49      ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
% 7.69/1.49      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 7.69/1.49      | v1_funct_1(sK4(X0,X1,sK7)) ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_30]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5667,plain,
% 7.69/1.49      ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
% 7.69/1.49      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 7.69/1.49      | v1_funct_1(sK4(sK6,sK5,sK7)) ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_5561]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5669,plain,
% 7.69/1.49      ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) != iProver_top
% 7.69/1.49      | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
% 7.69/1.49      | v1_funct_1(sK4(sK6,sK5,sK7)) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_5667]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5668,plain,
% 7.69/1.49      ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_33]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5671,plain,
% 7.69/1.49      ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_5668]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_4506,plain,
% 7.69/1.49      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.69/1.49      theory(equality) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5762,plain,
% 7.69/1.49      ( v1_funct_1(X0)
% 7.69/1.49      | ~ v1_funct_1(sK4(sK6,sK5,sK7))
% 7.69/1.49      | X0 != sK4(sK6,sK5,sK7) ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_4506]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5763,plain,
% 7.69/1.49      ( X0 != sK4(sK6,sK5,sK7)
% 7.69/1.49      | v1_funct_1(X0) = iProver_top
% 7.69/1.49      | v1_funct_1(sK4(sK6,sK5,sK7)) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_5762]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5765,plain,
% 7.69/1.49      ( sK7 != sK4(sK6,sK5,sK7)
% 7.69/1.49      | v1_funct_1(sK4(sK6,sK5,sK7)) != iProver_top
% 7.69/1.49      | v1_funct_1(sK7) = iProver_top ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_5763]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_31,plain,
% 7.69/1.49      ( ~ sP0(X0,X1,X2)
% 7.69/1.49      | ~ r2_hidden(X3,X2)
% 7.69/1.49      | v1_relat_1(sK4(X0,X1,X3)) ),
% 7.69/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5575,plain,
% 7.69/1.49      ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
% 7.69/1.49      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 7.69/1.49      | v1_relat_1(sK4(X0,X1,sK7)) ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_31]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5782,plain,
% 7.69/1.49      ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
% 7.69/1.49      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 7.69/1.49      | v1_relat_1(sK4(sK6,sK5,sK7)) ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_5575]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5784,plain,
% 7.69/1.49      ( sP0(sK6,sK5,k1_funct_2(sK5,sK6)) != iProver_top
% 7.69/1.49      | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top
% 7.69/1.49      | v1_relat_1(sK4(sK6,sK5,sK7)) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_5782]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5606,plain,
% 7.69/1.49      ( ~ sP0(X0,X1,k1_funct_2(sK5,sK6))
% 7.69/1.49      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 7.69/1.49      | sK4(X0,X1,sK7) = sK7 ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_29]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5781,plain,
% 7.69/1.49      ( ~ sP0(sK6,sK5,k1_funct_2(sK5,sK6))
% 7.69/1.49      | ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 7.69/1.49      | sK4(sK6,sK5,sK7) = sK7 ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_5606]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_4503,plain,
% 7.69/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.69/1.49      theory(equality) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5910,plain,
% 7.69/1.49      ( v1_relat_1(X0)
% 7.69/1.49      | ~ v1_relat_1(sK4(sK6,sK5,sK7))
% 7.69/1.49      | X0 != sK4(sK6,sK5,sK7) ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_4503]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5921,plain,
% 7.69/1.49      ( X0 != sK4(sK6,sK5,sK7)
% 7.69/1.49      | v1_relat_1(X0) = iProver_top
% 7.69/1.49      | v1_relat_1(sK4(sK6,sK5,sK7)) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_5910]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5923,plain,
% 7.69/1.49      ( sK7 != sK4(sK6,sK5,sK7)
% 7.69/1.49      | v1_relat_1(sK4(sK6,sK5,sK7)) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) = iProver_top ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_5921]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_4496,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6007,plain,
% 7.69/1.49      ( X0 != X1 | X0 = sK4(sK6,sK5,sK7) | sK4(sK6,sK5,sK7) != X1 ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_4496]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6008,plain,
% 7.69/1.49      ( sK4(sK6,sK5,sK7) != sK7 | sK7 = sK4(sK6,sK5,sK7) | sK7 != sK7 ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_6007]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8763,plain,
% 7.69/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_7281,c_38,c_39,c_125,c_129,c_643,c_5669,c_5668,c_5671,
% 7.69/1.49                 c_5765,c_5784,c_5781,c_5923,c_6008,c_7246]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8770,plain,
% 7.69/1.49      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 7.69/1.49      | r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5277,c_8763]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8775,plain,
% 7.69/1.49      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 7.69/1.49      | r1_tarski(sK5,sK5) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(light_normalisation,[status(thm)],[c_8770,c_7246]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8866,plain,
% 7.69/1.49      ( r1_tarski(sK5,sK5) != iProver_top
% 7.69/1.49      | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_8775,c_38,c_39,c_125,c_129,c_5668,c_5671,c_5784,
% 7.69/1.49                 c_5781,c_5923,c_6008]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8867,plain,
% 7.69/1.49      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 7.69/1.49      | r1_tarski(sK5,sK5) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(renaming,[status(thm)],[c_8866]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5282,plain,
% 7.69/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8873,plain,
% 7.69/1.49      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(forward_subsumption_resolution,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_8867,c_5282]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_10172,plain,
% 7.69/1.49      ( v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_10162,c_8873]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5262,plain,
% 7.69/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.69/1.49      | v1_funct_1(X0) != iProver_top
% 7.69/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7292,plain,
% 7.69/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(sK7)))) = iProver_top
% 7.69/1.49      | v1_funct_1(sK7) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_7246,c_5262]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7493,plain,
% 7.69/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_relat_1(sK7)))) = iProver_top ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_7292,c_38,c_39,c_125,c_129,c_5669,c_5668,c_5671,
% 7.69/1.49                 c_5765,c_5784,c_5781,c_5923,c_6008]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_13,plain,
% 7.69/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.49      | ~ v1_xboole_0(X2)
% 7.69/1.49      | v1_xboole_0(X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5278,plain,
% 7.69/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.69/1.49      | v1_xboole_0(X2) != iProver_top
% 7.69/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7499,plain,
% 7.69/1.49      ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top
% 7.69/1.49      | v1_xboole_0(sK7) = iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_7493,c_5278]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_10416,plain,
% 7.69/1.49      ( v1_xboole_0(sK7) = iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_10172,c_7499]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7,plain,
% 7.69/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.69/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5280,plain,
% 7.69/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.69/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6265,plain,
% 7.69/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.69/1.49      | v1_xboole_0(X2) != iProver_top
% 7.69/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5280,c_5278]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_10120,plain,
% 7.69/1.49      ( v1_xboole_0(X0) != iProver_top
% 7.69/1.49      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5282,c_6265]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_1,plain,
% 7.69/1.49      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.69/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5285,plain,
% 7.69/1.49      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 7.69/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_9,plain,
% 7.69/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.69/1.49      | ~ r2_hidden(X2,X0)
% 7.69/1.49      | ~ v1_xboole_0(X1) ),
% 7.69/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_291,plain,
% 7.69/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.69/1.49      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_292,plain,
% 7.69/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.69/1.49      inference(renaming,[status(thm)],[c_291]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_356,plain,
% 7.69/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 7.69/1.49      inference(bin_hyper_res,[status(thm)],[c_9,c_292]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5260,plain,
% 7.69/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.69/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.69/1.49      | v1_xboole_0(X2) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6013,plain,
% 7.69/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.69/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5282,c_5260]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6020,plain,
% 7.69/1.49      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5285,c_6013]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5283,plain,
% 7.69/1.49      ( X0 = X1
% 7.69/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.69/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6336,plain,
% 7.69/1.49      ( X0 = X1
% 7.69/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.69/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_6020,c_5283]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_6734,plain,
% 7.69/1.49      ( X0 = X1
% 7.69/1.49      | v1_xboole_0(X0) != iProver_top
% 7.69/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_6020,c_6336]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_11621,plain,
% 7.69/1.49      ( sK7 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_10416,c_6734]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_18172,plain,
% 7.69/1.49      ( k2_zfmisc_1(X0,X1) = sK7 | v1_xboole_0(X1) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_10120,c_11621]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_36310,plain,
% 7.69/1.49      ( k2_zfmisc_1(X0,sK7) = sK7 ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_10416,c_18172]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_12,plain,
% 7.69/1.49      ( v4_relat_1(X0,X1)
% 7.69/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.69/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_11,plain,
% 7.69/1.49      ( ~ v4_relat_1(X0,X1)
% 7.69/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.69/1.49      | ~ v1_relat_1(X0) ),
% 7.69/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_480,plain,
% 7.69/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.69/1.49      | ~ v1_relat_1(X0) ),
% 7.69/1.49      inference(resolution,[status(thm)],[c_12,c_11]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5259,plain,
% 7.69/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.69/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.69/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5831,plain,
% 7.69/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.69/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.69/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5280,c_5259]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_9779,plain,
% 7.69/1.49      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top
% 7.69/1.49      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5282,c_5831]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_36556,plain,
% 7.69/1.49      ( r1_tarski(k1_relat_1(sK7),X0) = iProver_top
% 7.69/1.49      | v1_relat_1(k2_zfmisc_1(X0,sK7)) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_36310,c_9779]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_36682,plain,
% 7.69/1.49      ( r1_tarski(sK5,X0) = iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.69/1.49      inference(light_normalisation,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_36556,c_7246,c_36310]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_36719,plain,
% 7.69/1.49      ( r1_tarski(sK5,X0) = iProver_top ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_36682,c_38,c_39,c_125,c_129,c_5668,c_5671,c_5784,
% 7.69/1.49                 c_5781,c_5923,c_6008]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_36728,plain,
% 7.69/1.49      ( sK5 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_36719,c_6336]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_36812,plain,
% 7.69/1.49      ( sK5 = sK7 | v1_xboole_0(sK7) != iProver_top ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_36728]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_4501,plain,
% 7.69/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.69/1.49      theory(equality) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_25135,plain,
% 7.69/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_4501]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_25137,plain,
% 7.69/1.49      ( v1_xboole_0(sK5) | ~ v1_xboole_0(sK7) | sK5 != sK7 ),
% 7.69/1.49      inference(instantiation,[status(thm)],[c_25135]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_10028,plain,
% 7.69/1.49      ( ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
% 7.69/1.49      | r1_tarski(k2_relat_1(sK7),sK6) ),
% 7.69/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_9981]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8874,plain,
% 7.69/1.49      ( ~ r1_tarski(k2_relat_1(sK7),sK6) | v1_xboole_0(k2_relat_1(sK7)) ),
% 7.69/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_8873]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_17,plain,
% 7.69/1.49      ( v1_partfun1(X0,X1)
% 7.69/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.49      | ~ v1_xboole_0(X1) ),
% 7.69/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_623,plain,
% 7.69/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.69/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.69/1.49      | ~ v1_funct_1(sK7)
% 7.69/1.49      | ~ v1_xboole_0(X1)
% 7.69/1.49      | sK5 != X1
% 7.69/1.49      | sK7 != X0 ),
% 7.69/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_577]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_624,plain,
% 7.69/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
% 7.69/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.69/1.49      | ~ v1_funct_1(sK7)
% 7.69/1.49      | ~ v1_xboole_0(sK5) ),
% 7.69/1.49      inference(unflattening,[status(thm)],[c_623]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_4493,plain,
% 7.69/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.69/1.49      | ~ v1_funct_1(sK7)
% 7.69/1.49      | ~ v1_xboole_0(sK5)
% 7.69/1.49      | sP0_iProver_split ),
% 7.69/1.49      inference(splitting,
% 7.69/1.49                [splitting(split),new_symbols(definition,[])],
% 7.69/1.49                [c_624]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5256,plain,
% 7.69/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.69/1.49      | v1_funct_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(sK5) != iProver_top
% 7.69/1.49      | sP0_iProver_split = iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_4493]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_4492,plain,
% 7.69/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
% 7.69/1.49      | ~ sP0_iProver_split ),
% 7.69/1.49      inference(splitting,
% 7.69/1.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.69/1.49                [c_624]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5257,plain,
% 7.69/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) != iProver_top
% 7.69/1.49      | sP0_iProver_split != iProver_top ),
% 7.69/1.49      inference(predicate_to_equality,[status(thm)],[c_4492]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_5411,plain,
% 7.69/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.69/1.49      | v1_funct_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.69/1.49      inference(forward_subsumption_resolution,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_5256,c_5257]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7969,plain,
% 7.69/1.49      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 7.69/1.49      | r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
% 7.69/1.49      | v1_funct_1(sK7) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.69/1.49      inference(superposition,[status(thm)],[c_5277,c_5411]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7976,plain,
% 7.69/1.49      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 7.69/1.49      | r1_tarski(sK5,sK5) != iProver_top
% 7.69/1.49      | v1_funct_1(sK7) != iProver_top
% 7.69/1.49      | v1_relat_1(sK7) != iProver_top
% 7.69/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.69/1.49      inference(light_normalisation,[status(thm)],[c_7969,c_7246]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8425,plain,
% 7.69/1.49      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 7.69/1.49      | r1_tarski(sK5,sK5) != iProver_top
% 7.69/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.69/1.49      inference(global_propositional_subsumption,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_7976,c_38,c_39,c_125,c_129,c_5669,c_5668,c_5671,
% 7.69/1.49                 c_5765,c_5784,c_5781,c_5923,c_6008]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8432,plain,
% 7.69/1.49      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 7.69/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.69/1.49      inference(forward_subsumption_resolution,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_8425,c_5282]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_8433,plain,
% 7.69/1.49      ( ~ r1_tarski(k2_relat_1(sK7),sK6) | ~ v1_xboole_0(sK5) ),
% 7.69/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_8432]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(c_7514,plain,
% 7.69/1.49      ( ~ v1_xboole_0(k2_relat_1(sK7)) | v1_xboole_0(sK7) ),
% 7.69/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_7499]) ).
% 7.69/1.49  
% 7.69/1.49  cnf(contradiction,plain,
% 7.69/1.49      ( $false ),
% 7.69/1.49      inference(minisat,
% 7.69/1.49                [status(thm)],
% 7.69/1.49                [c_36812,c_25137,c_10028,c_9981,c_8874,c_8873,c_8433,
% 7.69/1.49                 c_7514,c_7499,c_39,c_38]) ).
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.69/1.49  
% 7.69/1.49  ------                               Statistics
% 7.69/1.49  
% 7.69/1.49  ------ General
% 7.69/1.49  
% 7.69/1.49  abstr_ref_over_cycles:                  0
% 7.69/1.49  abstr_ref_under_cycles:                 0
% 7.69/1.49  gc_basic_clause_elim:                   0
% 7.69/1.49  forced_gc_time:                         0
% 7.69/1.49  parsing_time:                           0.011
% 7.69/1.49  unif_index_cands_time:                  0.
% 7.69/1.49  unif_index_add_time:                    0.
% 7.69/1.49  orderings_time:                         0.
% 7.69/1.49  out_proof_time:                         0.014
% 7.69/1.49  total_time:                             0.876
% 7.69/1.49  num_of_symbols:                         54
% 7.69/1.49  num_of_terms:                           27379
% 7.69/1.49  
% 7.69/1.49  ------ Preprocessing
% 7.69/1.49  
% 7.69/1.49  num_of_splits:                          1
% 7.69/1.49  num_of_split_atoms:                     1
% 7.69/1.49  num_of_reused_defs:                     0
% 7.69/1.49  num_eq_ax_congr_red:                    41
% 7.69/1.49  num_of_sem_filtered_clauses:            1
% 7.69/1.49  num_of_subtypes:                        0
% 7.69/1.49  monotx_restored_types:                  0
% 7.69/1.49  sat_num_of_epr_types:                   0
% 7.69/1.49  sat_num_of_non_cyclic_types:            0
% 7.69/1.49  sat_guarded_non_collapsed_types:        0
% 7.69/1.49  num_pure_diseq_elim:                    0
% 7.69/1.49  simp_replaced_by:                       0
% 7.69/1.49  res_preprocessed:                       161
% 7.69/1.49  prep_upred:                             0
% 7.69/1.49  prep_unflattend:                        150
% 7.69/1.49  smt_new_axioms:                         0
% 7.69/1.49  pred_elim_cands:                        7
% 7.69/1.49  pred_elim:                              3
% 7.69/1.49  pred_elim_cl:                           4
% 7.69/1.49  pred_elim_cycles:                       10
% 7.69/1.49  merged_defs:                            8
% 7.69/1.49  merged_defs_ncl:                        0
% 7.69/1.49  bin_hyper_res:                          9
% 7.69/1.49  prep_cycles:                            4
% 7.69/1.49  pred_elim_time:                         0.085
% 7.69/1.49  splitting_time:                         0.
% 7.69/1.49  sem_filter_time:                        0.
% 7.69/1.49  monotx_time:                            0.
% 7.69/1.49  subtype_inf_time:                       0.
% 7.69/1.49  
% 7.69/1.49  ------ Problem properties
% 7.69/1.49  
% 7.69/1.49  clauses:                                32
% 7.69/1.49  conjectures:                            1
% 7.69/1.49  epr:                                    5
% 7.69/1.49  horn:                                   26
% 7.69/1.49  ground:                                 4
% 7.69/1.49  unary:                                  3
% 7.69/1.49  binary:                                 6
% 7.69/1.49  lits:                                   95
% 7.69/1.49  lits_eq:                                10
% 7.69/1.49  fd_pure:                                0
% 7.69/1.49  fd_pseudo:                              0
% 7.69/1.49  fd_cond:                                0
% 7.69/1.49  fd_pseudo_cond:                         2
% 7.69/1.49  ac_symbols:                             0
% 7.69/1.49  
% 7.69/1.49  ------ Propositional Solver
% 7.69/1.49  
% 7.69/1.49  prop_solver_calls:                      30
% 7.69/1.49  prop_fast_solver_calls:                 2846
% 7.69/1.49  smt_solver_calls:                       0
% 7.69/1.49  smt_fast_solver_calls:                  0
% 7.69/1.49  prop_num_of_clauses:                    11382
% 7.69/1.49  prop_preprocess_simplified:             22006
% 7.69/1.49  prop_fo_subsumed:                       109
% 7.69/1.49  prop_solver_time:                       0.
% 7.69/1.49  smt_solver_time:                        0.
% 7.69/1.49  smt_fast_solver_time:                   0.
% 7.69/1.49  prop_fast_solver_time:                  0.
% 7.69/1.49  prop_unsat_core_time:                   0.001
% 7.69/1.49  
% 7.69/1.49  ------ QBF
% 7.69/1.49  
% 7.69/1.49  qbf_q_res:                              0
% 7.69/1.49  qbf_num_tautologies:                    0
% 7.69/1.49  qbf_prep_cycles:                        0
% 7.69/1.49  
% 7.69/1.49  ------ BMC1
% 7.69/1.49  
% 7.69/1.49  bmc1_current_bound:                     -1
% 7.69/1.49  bmc1_last_solved_bound:                 -1
% 7.69/1.49  bmc1_unsat_core_size:                   -1
% 7.69/1.49  bmc1_unsat_core_parents_size:           -1
% 7.69/1.49  bmc1_merge_next_fun:                    0
% 7.69/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.69/1.49  
% 7.69/1.49  ------ Instantiation
% 7.69/1.49  
% 7.69/1.49  inst_num_of_clauses:                    2445
% 7.69/1.49  inst_num_in_passive:                    740
% 7.69/1.49  inst_num_in_active:                     937
% 7.69/1.49  inst_num_in_unprocessed:                768
% 7.69/1.49  inst_num_of_loops:                      1300
% 7.69/1.49  inst_num_of_learning_restarts:          0
% 7.69/1.49  inst_num_moves_active_passive:          360
% 7.69/1.49  inst_lit_activity:                      0
% 7.69/1.49  inst_lit_activity_moves:                0
% 7.69/1.49  inst_num_tautologies:                   0
% 7.69/1.49  inst_num_prop_implied:                  0
% 7.69/1.49  inst_num_existing_simplified:           0
% 7.69/1.49  inst_num_eq_res_simplified:             0
% 7.69/1.49  inst_num_child_elim:                    0
% 7.69/1.49  inst_num_of_dismatching_blockings:      2290
% 7.69/1.49  inst_num_of_non_proper_insts:           3052
% 7.69/1.49  inst_num_of_duplicates:                 0
% 7.69/1.49  inst_inst_num_from_inst_to_res:         0
% 7.69/1.49  inst_dismatching_checking_time:         0.
% 7.69/1.49  
% 7.69/1.49  ------ Resolution
% 7.69/1.49  
% 7.69/1.49  res_num_of_clauses:                     0
% 7.69/1.49  res_num_in_passive:                     0
% 7.69/1.49  res_num_in_active:                      0
% 7.69/1.49  res_num_of_loops:                       165
% 7.69/1.49  res_forward_subset_subsumed:            173
% 7.69/1.49  res_backward_subset_subsumed:           0
% 7.69/1.49  res_forward_subsumed:                   0
% 7.69/1.49  res_backward_subsumed:                  0
% 7.69/1.49  res_forward_subsumption_resolution:     2
% 7.69/1.49  res_backward_subsumption_resolution:    0
% 7.69/1.49  res_clause_to_clause_subsumption:       4684
% 7.69/1.49  res_orphan_elimination:                 0
% 7.69/1.49  res_tautology_del:                      364
% 7.69/1.49  res_num_eq_res_simplified:              0
% 7.69/1.49  res_num_sel_changes:                    0
% 7.69/1.49  res_moves_from_active_to_pass:          0
% 7.69/1.49  
% 7.69/1.49  ------ Superposition
% 7.69/1.49  
% 7.69/1.49  sup_time_total:                         0.
% 7.69/1.49  sup_time_generating:                    0.
% 7.69/1.49  sup_time_sim_full:                      0.
% 7.69/1.49  sup_time_sim_immed:                     0.
% 7.69/1.49  
% 7.69/1.49  sup_num_of_clauses:                     873
% 7.69/1.49  sup_num_in_active:                      206
% 7.69/1.49  sup_num_in_passive:                     667
% 7.69/1.49  sup_num_of_loops:                       259
% 7.69/1.49  sup_fw_superposition:                   491
% 7.69/1.49  sup_bw_superposition:                   750
% 7.69/1.49  sup_immediate_simplified:               223
% 7.69/1.49  sup_given_eliminated:                   2
% 7.69/1.49  comparisons_done:                       0
% 7.69/1.49  comparisons_avoided:                    57
% 7.69/1.49  
% 7.69/1.49  ------ Simplifications
% 7.69/1.49  
% 7.69/1.49  
% 7.69/1.49  sim_fw_subset_subsumed:                 99
% 7.69/1.49  sim_bw_subset_subsumed:                 12
% 7.69/1.49  sim_fw_subsumed:                        82
% 7.69/1.49  sim_bw_subsumed:                        12
% 7.69/1.49  sim_fw_subsumption_res:                 5
% 7.69/1.49  sim_bw_subsumption_res:                 0
% 7.69/1.49  sim_tautology_del:                      12
% 7.69/1.49  sim_eq_tautology_del:                   17
% 7.69/1.49  sim_eq_res_simp:                        2
% 7.69/1.49  sim_fw_demodulated:                     13
% 7.69/1.49  sim_bw_demodulated:                     50
% 7.69/1.49  sim_light_normalised:                   83
% 7.69/1.49  sim_joinable_taut:                      0
% 7.69/1.49  sim_joinable_simp:                      0
% 7.69/1.49  sim_ac_normalised:                      0
% 7.69/1.49  sim_smt_subsumption:                    0
% 7.69/1.49  
%------------------------------------------------------------------------------

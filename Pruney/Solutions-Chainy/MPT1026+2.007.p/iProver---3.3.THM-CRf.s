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
% DateTime   : Thu Dec  3 12:08:13 EST 2020

% Result     : Theorem 19.59s
% Output     : CNFRefutation 19.59s
% Verified   : 
% Statistics : Number of formulae       :  147 (1537 expanded)
%              Number of clauses        :   79 ( 488 expanded)
%              Number of leaves         :   19 ( 399 expanded)
%              Depth                    :   18
%              Number of atoms          :  646 (9758 expanded)
%              Number of equality atoms :  226 (2902 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f62,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
        | ~ v1_funct_2(sK16,sK14,sK15)
        | ~ v1_funct_1(sK16) )
      & r2_hidden(sK16,k1_funct_2(sK14,sK15)) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
      | ~ v1_funct_2(sK16,sK14,sK15)
      | ~ v1_funct_1(sK16) )
    & r2_hidden(sK16,k1_funct_2(sK14,sK15)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f27,f59])).

fof(f103,plain,(
    r2_hidden(sK16,k1_funct_2(sK14,sK15)) ),
    inference(cnf_transformation,[],[f60])).

fof(f10,axiom,(
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

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f10,f28])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f116,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f98])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f56,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK13(X0,X1,X6)),X0)
        & k1_relat_1(sK13(X0,X1,X6)) = X1
        & sK13(X0,X1,X6) = X6
        & v1_funct_1(sK13(X0,X1,X6))
        & v1_relat_1(sK13(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK12(X0,X1,X2)),X0)
        & k1_relat_1(sK12(X0,X1,X2)) = X1
        & sK12(X0,X1,X2) = X3
        & v1_funct_1(sK12(X0,X1,X2))
        & v1_relat_1(sK12(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
              | sK11(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK11(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK11(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK12(X0,X1,X2)),X0)
              & k1_relat_1(sK12(X0,X1,X2)) = X1
              & sK11(X0,X1,X2) = sK12(X0,X1,X2)
              & v1_funct_1(sK12(X0,X1,X2))
              & v1_relat_1(sK12(X0,X1,X2)) )
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK13(X0,X1,X6)),X0)
                & k1_relat_1(sK13(X0,X1,X6)) = X1
                & sK13(X0,X1,X6) = X6
                & v1_funct_1(sK13(X0,X1,X6))
                & v1_relat_1(sK13(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f53,f56,f55,f54])).

fof(f89,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK13(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    ! [X6,X2,X0,X1] :
      ( sK13(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f46,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) = X2
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1)
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f43,f46,f45,f44])).

fof(f72,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f110,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK13(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK13(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f101,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f104,plain,
    ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
    | ~ v1_funct_2(sK16,sK14,sK15)
    | ~ v1_funct_1(sK16) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f90,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK13(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_0,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8576,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_43,negated_conjecture,
    ( r2_hidden(sK16,k1_funct_2(sK14,sK15)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_8542,plain,
    ( r2_hidden(sK16,k1_funct_2(sK14,sK15)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_38,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_8544,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_33,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK13(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_8549,plain,
    ( k1_relat_1(sK13(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10566,plain,
    ( k1_relat_1(sK13(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_8549])).

cnf(c_11642,plain,
    ( k1_relat_1(sK13(sK15,sK14,sK16)) = sK14 ),
    inference(superposition,[status(thm)],[c_8542,c_10566])).

cnf(c_34,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK13(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_8548,plain,
    ( sK13(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9834,plain,
    ( sK13(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_8548])).

cnf(c_10087,plain,
    ( sK13(sK15,sK14,sK16) = sK16 ),
    inference(superposition,[status(thm)],[c_8542,c_9834])).

cnf(c_11643,plain,
    ( k1_relat_1(sK16) = sK14 ),
    inference(light_normalisation,[status(thm)],[c_11642,c_10087])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_8565,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8575,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12684,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8565,c_8575])).

cnf(c_62359,plain,
    ( r2_hidden(X0,sK14) != iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_funct_1(sK16) != iProver_top
    | v1_xboole_0(k2_relat_1(sK16)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11643,c_12684])).

cnf(c_44,plain,
    ( r2_hidden(sK16,k1_funct_2(sK14,sK15)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_36,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK13(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_8546,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_relat_1(sK13(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9681,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_relat_1(sK13(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_8546])).

cnf(c_10942,plain,
    ( v1_relat_1(sK13(sK15,sK14,sK16)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8542,c_9681])).

cnf(c_10943,plain,
    ( v1_relat_1(sK16) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10942,c_10087])).

cnf(c_35,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK13(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_8547,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_funct_1(sK13(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_9873,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_funct_1(sK13(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_8547])).

cnf(c_11036,plain,
    ( v1_funct_1(sK13(sK15,sK14,sK16)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8542,c_9873])).

cnf(c_11037,plain,
    ( v1_funct_1(sK16) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11036,c_10087])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8558,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_620,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k1_relat_1(X3) != X1
    | k2_relat_1(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_40])).

cnf(c_621,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_39,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_625,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_621,c_39])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_42,negated_conjecture,
    ( ~ v1_funct_2(sK16,sK14,sK15)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
    | ~ v1_funct_1(sK16) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_644,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK16)
    | sK15 != X2
    | sK14 != X1
    | sK16 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_42])).

cnf(c_645,plain,
    ( ~ v1_partfun1(sK16,sK14)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
    | ~ v1_funct_1(sK16) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_709,plain,
    ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK16)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK14
    | sK16 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_625,c_645])).

cnf(c_710,plain,
    ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
    | ~ v1_relat_1(sK16)
    | ~ v1_funct_1(sK16)
    | v1_xboole_0(k2_relat_1(sK16))
    | k1_relat_1(sK16) != sK14 ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_8538,plain,
    ( k1_relat_1(sK16) != sK14
    | m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_funct_1(sK16) != iProver_top
    | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_11664,plain,
    ( sK14 != sK14
    | m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_funct_1(sK16) != iProver_top
    | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11643,c_8538])).

cnf(c_11667,plain,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_funct_1(sK16) != iProver_top
    | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11664])).

cnf(c_711,plain,
    ( k1_relat_1(sK16) != sK14
    | m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_funct_1(sK16) != iProver_top
    | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_11984,plain,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11667,c_711,c_10943,c_11037,c_11643])).

cnf(c_13265,plain,
    ( r1_tarski(k1_relat_1(sK16),sK14) != iProver_top
    | r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8558,c_11984])).

cnf(c_13268,plain,
    ( r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
    | r1_tarski(sK14,sK14) != iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13265,c_11643])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_11627,plain,
    ( r1_tarski(sK14,sK14) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11628,plain,
    ( r1_tarski(sK14,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11627])).

cnf(c_13564,plain,
    ( r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
    | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13268,c_10943,c_11628])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK13(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_8550,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK13(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10850,plain,
    ( r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8544,c_8550])).

cnf(c_23170,plain,
    ( r1_tarski(k2_relat_1(sK16),sK15) = iProver_top
    | r2_hidden(sK16,k1_funct_2(sK14,sK15)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10087,c_10850])).

cnf(c_62431,plain,
    ( r2_hidden(X0,sK14) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62359,c_44,c_10943,c_11037,c_11628,c_13268,c_23170])).

cnf(c_62437,plain,
    ( v1_xboole_0(sK14) = iProver_top ),
    inference(superposition,[status(thm)],[c_8576,c_62431])).

cnf(c_22,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_691,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
    | ~ v1_funct_1(sK16)
    | ~ v1_xboole_0(X1)
    | sK14 != X1
    | sK16 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_645])).

cnf(c_692,plain,
    ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,X0)))
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
    | ~ v1_funct_1(sK16)
    | ~ v1_xboole_0(sK14) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_7886,plain,
    ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
    | ~ v1_funct_1(sK16)
    | ~ v1_xboole_0(sK14)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_692])).

cnf(c_8539,plain,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
    | v1_funct_1(sK16) != iProver_top
    | v1_xboole_0(sK14) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7886])).

cnf(c_13266,plain,
    ( r1_tarski(k1_relat_1(sK16),sK14) != iProver_top
    | r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_funct_1(sK16) != iProver_top
    | v1_xboole_0(sK14) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_8558,c_8539])).

cnf(c_13267,plain,
    ( r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
    | r1_tarski(sK14,sK14) != iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_funct_1(sK16) != iProver_top
    | v1_xboole_0(sK14) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13266,c_11643])).

cnf(c_8543,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_11670,plain,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,k2_relat_1(sK16)))) = iProver_top
    | v1_relat_1(sK16) != iProver_top
    | v1_funct_1(sK16) != iProver_top ),
    inference(superposition,[status(thm)],[c_11643,c_8543])).

cnf(c_11768,plain,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,k2_relat_1(sK16)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11670,c_10943,c_11037])).

cnf(c_7885,plain,
    ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_692])).

cnf(c_8540,plain,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7885])).

cnf(c_11772,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_11768,c_8540])).

cnf(c_13569,plain,
    ( v1_xboole_0(sK14) != iProver_top
    | r1_tarski(k2_relat_1(sK16),sK15) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13267,c_10943,c_11037,c_11628,c_11772])).

cnf(c_13570,plain,
    ( r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
    | v1_xboole_0(sK14) != iProver_top ),
    inference(renaming,[status(thm)],[c_13569])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62437,c_23170,c_13570,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.59/3.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.59/3.01  
% 19.59/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.59/3.01  
% 19.59/3.01  ------  iProver source info
% 19.59/3.01  
% 19.59/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.59/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.59/3.01  git: non_committed_changes: false
% 19.59/3.01  git: last_make_outside_of_git: false
% 19.59/3.01  
% 19.59/3.01  ------ 
% 19.59/3.01  
% 19.59/3.01  ------ Input Options
% 19.59/3.01  
% 19.59/3.01  --out_options                           all
% 19.59/3.01  --tptp_safe_out                         true
% 19.59/3.01  --problem_path                          ""
% 19.59/3.01  --include_path                          ""
% 19.59/3.01  --clausifier                            res/vclausify_rel
% 19.59/3.01  --clausifier_options                    ""
% 19.59/3.01  --stdin                                 false
% 19.59/3.01  --stats_out                             all
% 19.59/3.01  
% 19.59/3.01  ------ General Options
% 19.59/3.01  
% 19.59/3.01  --fof                                   false
% 19.59/3.01  --time_out_real                         305.
% 19.59/3.01  --time_out_virtual                      -1.
% 19.59/3.01  --symbol_type_check                     false
% 19.59/3.01  --clausify_out                          false
% 19.59/3.01  --sig_cnt_out                           false
% 19.59/3.01  --trig_cnt_out                          false
% 19.59/3.01  --trig_cnt_out_tolerance                1.
% 19.59/3.01  --trig_cnt_out_sk_spl                   false
% 19.59/3.01  --abstr_cl_out                          false
% 19.59/3.01  
% 19.59/3.01  ------ Global Options
% 19.59/3.01  
% 19.59/3.01  --schedule                              default
% 19.59/3.01  --add_important_lit                     false
% 19.59/3.01  --prop_solver_per_cl                    1000
% 19.59/3.01  --min_unsat_core                        false
% 19.59/3.01  --soft_assumptions                      false
% 19.59/3.01  --soft_lemma_size                       3
% 19.59/3.01  --prop_impl_unit_size                   0
% 19.59/3.01  --prop_impl_unit                        []
% 19.59/3.01  --share_sel_clauses                     true
% 19.59/3.01  --reset_solvers                         false
% 19.59/3.01  --bc_imp_inh                            [conj_cone]
% 19.59/3.01  --conj_cone_tolerance                   3.
% 19.59/3.01  --extra_neg_conj                        none
% 19.59/3.01  --large_theory_mode                     true
% 19.59/3.01  --prolific_symb_bound                   200
% 19.59/3.01  --lt_threshold                          2000
% 19.59/3.01  --clause_weak_htbl                      true
% 19.59/3.01  --gc_record_bc_elim                     false
% 19.59/3.01  
% 19.59/3.01  ------ Preprocessing Options
% 19.59/3.01  
% 19.59/3.01  --preprocessing_flag                    true
% 19.59/3.01  --time_out_prep_mult                    0.1
% 19.59/3.01  --splitting_mode                        input
% 19.59/3.01  --splitting_grd                         true
% 19.59/3.01  --splitting_cvd                         false
% 19.59/3.01  --splitting_cvd_svl                     false
% 19.59/3.01  --splitting_nvd                         32
% 19.59/3.01  --sub_typing                            true
% 19.59/3.01  --prep_gs_sim                           true
% 19.59/3.01  --prep_unflatten                        true
% 19.59/3.01  --prep_res_sim                          true
% 19.59/3.01  --prep_upred                            true
% 19.59/3.01  --prep_sem_filter                       exhaustive
% 19.59/3.01  --prep_sem_filter_out                   false
% 19.59/3.01  --pred_elim                             true
% 19.59/3.01  --res_sim_input                         true
% 19.59/3.01  --eq_ax_congr_red                       true
% 19.59/3.01  --pure_diseq_elim                       true
% 19.59/3.01  --brand_transform                       false
% 19.59/3.01  --non_eq_to_eq                          false
% 19.59/3.01  --prep_def_merge                        true
% 19.59/3.01  --prep_def_merge_prop_impl              false
% 19.59/3.01  --prep_def_merge_mbd                    true
% 19.59/3.01  --prep_def_merge_tr_red                 false
% 19.59/3.01  --prep_def_merge_tr_cl                  false
% 19.59/3.01  --smt_preprocessing                     true
% 19.59/3.01  --smt_ac_axioms                         fast
% 19.59/3.01  --preprocessed_out                      false
% 19.59/3.01  --preprocessed_stats                    false
% 19.59/3.01  
% 19.59/3.01  ------ Abstraction refinement Options
% 19.59/3.01  
% 19.59/3.01  --abstr_ref                             []
% 19.59/3.01  --abstr_ref_prep                        false
% 19.59/3.01  --abstr_ref_until_sat                   false
% 19.59/3.01  --abstr_ref_sig_restrict                funpre
% 19.59/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.59/3.01  --abstr_ref_under                       []
% 19.59/3.01  
% 19.59/3.01  ------ SAT Options
% 19.59/3.01  
% 19.59/3.01  --sat_mode                              false
% 19.59/3.01  --sat_fm_restart_options                ""
% 19.59/3.01  --sat_gr_def                            false
% 19.59/3.01  --sat_epr_types                         true
% 19.59/3.01  --sat_non_cyclic_types                  false
% 19.59/3.01  --sat_finite_models                     false
% 19.59/3.01  --sat_fm_lemmas                         false
% 19.59/3.01  --sat_fm_prep                           false
% 19.59/3.01  --sat_fm_uc_incr                        true
% 19.59/3.01  --sat_out_model                         small
% 19.59/3.01  --sat_out_clauses                       false
% 19.59/3.01  
% 19.59/3.01  ------ QBF Options
% 19.59/3.01  
% 19.59/3.01  --qbf_mode                              false
% 19.59/3.01  --qbf_elim_univ                         false
% 19.59/3.01  --qbf_dom_inst                          none
% 19.59/3.01  --qbf_dom_pre_inst                      false
% 19.59/3.01  --qbf_sk_in                             false
% 19.59/3.01  --qbf_pred_elim                         true
% 19.59/3.01  --qbf_split                             512
% 19.59/3.01  
% 19.59/3.01  ------ BMC1 Options
% 19.59/3.01  
% 19.59/3.01  --bmc1_incremental                      false
% 19.59/3.01  --bmc1_axioms                           reachable_all
% 19.59/3.01  --bmc1_min_bound                        0
% 19.59/3.01  --bmc1_max_bound                        -1
% 19.59/3.01  --bmc1_max_bound_default                -1
% 19.59/3.01  --bmc1_symbol_reachability              true
% 19.59/3.01  --bmc1_property_lemmas                  false
% 19.59/3.01  --bmc1_k_induction                      false
% 19.59/3.01  --bmc1_non_equiv_states                 false
% 19.59/3.01  --bmc1_deadlock                         false
% 19.59/3.01  --bmc1_ucm                              false
% 19.59/3.01  --bmc1_add_unsat_core                   none
% 19.59/3.01  --bmc1_unsat_core_children              false
% 19.59/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.59/3.01  --bmc1_out_stat                         full
% 19.59/3.01  --bmc1_ground_init                      false
% 19.59/3.01  --bmc1_pre_inst_next_state              false
% 19.59/3.01  --bmc1_pre_inst_state                   false
% 19.59/3.01  --bmc1_pre_inst_reach_state             false
% 19.59/3.01  --bmc1_out_unsat_core                   false
% 19.59/3.01  --bmc1_aig_witness_out                  false
% 19.59/3.01  --bmc1_verbose                          false
% 19.59/3.01  --bmc1_dump_clauses_tptp                false
% 19.59/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.59/3.01  --bmc1_dump_file                        -
% 19.59/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.59/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.59/3.01  --bmc1_ucm_extend_mode                  1
% 19.59/3.01  --bmc1_ucm_init_mode                    2
% 19.59/3.01  --bmc1_ucm_cone_mode                    none
% 19.59/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.59/3.01  --bmc1_ucm_relax_model                  4
% 19.59/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.59/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.59/3.01  --bmc1_ucm_layered_model                none
% 19.59/3.01  --bmc1_ucm_max_lemma_size               10
% 19.59/3.01  
% 19.59/3.01  ------ AIG Options
% 19.59/3.01  
% 19.59/3.01  --aig_mode                              false
% 19.59/3.01  
% 19.59/3.01  ------ Instantiation Options
% 19.59/3.01  
% 19.59/3.01  --instantiation_flag                    true
% 19.59/3.01  --inst_sos_flag                         true
% 19.59/3.01  --inst_sos_phase                        true
% 19.59/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.59/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.59/3.01  --inst_lit_sel_side                     num_symb
% 19.59/3.01  --inst_solver_per_active                1400
% 19.59/3.01  --inst_solver_calls_frac                1.
% 19.59/3.01  --inst_passive_queue_type               priority_queues
% 19.59/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.59/3.01  --inst_passive_queues_freq              [25;2]
% 19.59/3.01  --inst_dismatching                      true
% 19.59/3.01  --inst_eager_unprocessed_to_passive     true
% 19.59/3.01  --inst_prop_sim_given                   true
% 19.59/3.01  --inst_prop_sim_new                     false
% 19.59/3.01  --inst_subs_new                         false
% 19.59/3.01  --inst_eq_res_simp                      false
% 19.59/3.01  --inst_subs_given                       false
% 19.59/3.01  --inst_orphan_elimination               true
% 19.59/3.01  --inst_learning_loop_flag               true
% 19.59/3.01  --inst_learning_start                   3000
% 19.59/3.01  --inst_learning_factor                  2
% 19.59/3.01  --inst_start_prop_sim_after_learn       3
% 19.59/3.01  --inst_sel_renew                        solver
% 19.59/3.01  --inst_lit_activity_flag                true
% 19.59/3.01  --inst_restr_to_given                   false
% 19.59/3.01  --inst_activity_threshold               500
% 19.59/3.01  --inst_out_proof                        true
% 19.59/3.01  
% 19.59/3.01  ------ Resolution Options
% 19.59/3.01  
% 19.59/3.01  --resolution_flag                       true
% 19.59/3.01  --res_lit_sel                           adaptive
% 19.59/3.01  --res_lit_sel_side                      none
% 19.59/3.01  --res_ordering                          kbo
% 19.59/3.01  --res_to_prop_solver                    active
% 19.59/3.01  --res_prop_simpl_new                    false
% 19.59/3.01  --res_prop_simpl_given                  true
% 19.59/3.01  --res_passive_queue_type                priority_queues
% 19.59/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.59/3.01  --res_passive_queues_freq               [15;5]
% 19.59/3.01  --res_forward_subs                      full
% 19.59/3.01  --res_backward_subs                     full
% 19.59/3.01  --res_forward_subs_resolution           true
% 19.59/3.01  --res_backward_subs_resolution          true
% 19.59/3.01  --res_orphan_elimination                true
% 19.59/3.01  --res_time_limit                        2.
% 19.59/3.01  --res_out_proof                         true
% 19.59/3.01  
% 19.59/3.01  ------ Superposition Options
% 19.59/3.01  
% 19.59/3.01  --superposition_flag                    true
% 19.59/3.01  --sup_passive_queue_type                priority_queues
% 19.59/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.59/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.59/3.01  --demod_completeness_check              fast
% 19.59/3.01  --demod_use_ground                      true
% 19.59/3.01  --sup_to_prop_solver                    passive
% 19.59/3.01  --sup_prop_simpl_new                    true
% 19.59/3.01  --sup_prop_simpl_given                  true
% 19.59/3.01  --sup_fun_splitting                     true
% 19.59/3.01  --sup_smt_interval                      50000
% 19.59/3.01  
% 19.59/3.01  ------ Superposition Simplification Setup
% 19.59/3.01  
% 19.59/3.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.59/3.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.59/3.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.59/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.59/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.59/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.59/3.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.59/3.01  --sup_immed_triv                        [TrivRules]
% 19.59/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.59/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.59/3.01  --sup_immed_bw_main                     []
% 19.59/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.59/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.59/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.59/3.01  --sup_input_bw                          []
% 19.59/3.01  
% 19.59/3.01  ------ Combination Options
% 19.59/3.01  
% 19.59/3.01  --comb_res_mult                         3
% 19.59/3.01  --comb_sup_mult                         2
% 19.59/3.01  --comb_inst_mult                        10
% 19.59/3.01  
% 19.59/3.01  ------ Debug Options
% 19.59/3.01  
% 19.59/3.01  --dbg_backtrace                         false
% 19.59/3.01  --dbg_dump_prop_clauses                 false
% 19.59/3.01  --dbg_dump_prop_clauses_file            -
% 19.59/3.01  --dbg_out_stat                          false
% 19.59/3.01  ------ Parsing...
% 19.59/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.59/3.01  
% 19.59/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.59/3.01  
% 19.59/3.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.59/3.01  
% 19.59/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.59/3.01  ------ Proving...
% 19.59/3.01  ------ Problem Properties 
% 19.59/3.01  
% 19.59/3.01  
% 19.59/3.01  clauses                                 39
% 19.59/3.01  conjectures                             1
% 19.59/3.01  EPR                                     3
% 19.59/3.01  Horn                                    28
% 19.59/3.01  unary                                   3
% 19.59/3.01  binary                                  9
% 19.59/3.01  lits                                    124
% 19.59/3.01  lits eq                                 20
% 19.59/3.01  fd_pure                                 0
% 19.59/3.01  fd_pseudo                               0
% 19.59/3.01  fd_cond                                 0
% 19.59/3.01  fd_pseudo_cond                          8
% 19.59/3.01  AC symbols                              0
% 19.59/3.01  
% 19.59/3.01  ------ Schedule dynamic 5 is on 
% 19.59/3.01  
% 19.59/3.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.59/3.01  
% 19.59/3.01  
% 19.59/3.01  ------ 
% 19.59/3.01  Current options:
% 19.59/3.01  ------ 
% 19.59/3.01  
% 19.59/3.01  ------ Input Options
% 19.59/3.01  
% 19.59/3.01  --out_options                           all
% 19.59/3.01  --tptp_safe_out                         true
% 19.59/3.01  --problem_path                          ""
% 19.59/3.01  --include_path                          ""
% 19.59/3.01  --clausifier                            res/vclausify_rel
% 19.59/3.01  --clausifier_options                    ""
% 19.59/3.01  --stdin                                 false
% 19.59/3.01  --stats_out                             all
% 19.59/3.01  
% 19.59/3.01  ------ General Options
% 19.59/3.01  
% 19.59/3.01  --fof                                   false
% 19.59/3.01  --time_out_real                         305.
% 19.59/3.01  --time_out_virtual                      -1.
% 19.59/3.01  --symbol_type_check                     false
% 19.59/3.01  --clausify_out                          false
% 19.59/3.01  --sig_cnt_out                           false
% 19.59/3.01  --trig_cnt_out                          false
% 19.59/3.01  --trig_cnt_out_tolerance                1.
% 19.59/3.01  --trig_cnt_out_sk_spl                   false
% 19.59/3.01  --abstr_cl_out                          false
% 19.59/3.01  
% 19.59/3.01  ------ Global Options
% 19.59/3.01  
% 19.59/3.01  --schedule                              default
% 19.59/3.01  --add_important_lit                     false
% 19.59/3.01  --prop_solver_per_cl                    1000
% 19.59/3.01  --min_unsat_core                        false
% 19.59/3.01  --soft_assumptions                      false
% 19.59/3.01  --soft_lemma_size                       3
% 19.59/3.01  --prop_impl_unit_size                   0
% 19.59/3.01  --prop_impl_unit                        []
% 19.59/3.01  --share_sel_clauses                     true
% 19.59/3.01  --reset_solvers                         false
% 19.59/3.01  --bc_imp_inh                            [conj_cone]
% 19.59/3.01  --conj_cone_tolerance                   3.
% 19.59/3.01  --extra_neg_conj                        none
% 19.59/3.01  --large_theory_mode                     true
% 19.59/3.01  --prolific_symb_bound                   200
% 19.59/3.01  --lt_threshold                          2000
% 19.59/3.01  --clause_weak_htbl                      true
% 19.59/3.01  --gc_record_bc_elim                     false
% 19.59/3.01  
% 19.59/3.01  ------ Preprocessing Options
% 19.59/3.01  
% 19.59/3.01  --preprocessing_flag                    true
% 19.59/3.01  --time_out_prep_mult                    0.1
% 19.59/3.01  --splitting_mode                        input
% 19.59/3.01  --splitting_grd                         true
% 19.59/3.01  --splitting_cvd                         false
% 19.59/3.01  --splitting_cvd_svl                     false
% 19.59/3.01  --splitting_nvd                         32
% 19.59/3.01  --sub_typing                            true
% 19.59/3.01  --prep_gs_sim                           true
% 19.59/3.01  --prep_unflatten                        true
% 19.59/3.01  --prep_res_sim                          true
% 19.59/3.01  --prep_upred                            true
% 19.59/3.01  --prep_sem_filter                       exhaustive
% 19.59/3.01  --prep_sem_filter_out                   false
% 19.59/3.01  --pred_elim                             true
% 19.59/3.01  --res_sim_input                         true
% 19.59/3.01  --eq_ax_congr_red                       true
% 19.59/3.01  --pure_diseq_elim                       true
% 19.59/3.01  --brand_transform                       false
% 19.59/3.01  --non_eq_to_eq                          false
% 19.59/3.01  --prep_def_merge                        true
% 19.59/3.01  --prep_def_merge_prop_impl              false
% 19.59/3.01  --prep_def_merge_mbd                    true
% 19.59/3.01  --prep_def_merge_tr_red                 false
% 19.59/3.01  --prep_def_merge_tr_cl                  false
% 19.59/3.01  --smt_preprocessing                     true
% 19.59/3.01  --smt_ac_axioms                         fast
% 19.59/3.01  --preprocessed_out                      false
% 19.59/3.01  --preprocessed_stats                    false
% 19.59/3.01  
% 19.59/3.01  ------ Abstraction refinement Options
% 19.59/3.01  
% 19.59/3.01  --abstr_ref                             []
% 19.59/3.01  --abstr_ref_prep                        false
% 19.59/3.01  --abstr_ref_until_sat                   false
% 19.59/3.01  --abstr_ref_sig_restrict                funpre
% 19.59/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.59/3.01  --abstr_ref_under                       []
% 19.59/3.01  
% 19.59/3.01  ------ SAT Options
% 19.59/3.01  
% 19.59/3.01  --sat_mode                              false
% 19.59/3.01  --sat_fm_restart_options                ""
% 19.59/3.01  --sat_gr_def                            false
% 19.59/3.01  --sat_epr_types                         true
% 19.59/3.01  --sat_non_cyclic_types                  false
% 19.59/3.01  --sat_finite_models                     false
% 19.59/3.01  --sat_fm_lemmas                         false
% 19.59/3.01  --sat_fm_prep                           false
% 19.59/3.01  --sat_fm_uc_incr                        true
% 19.59/3.01  --sat_out_model                         small
% 19.59/3.01  --sat_out_clauses                       false
% 19.59/3.01  
% 19.59/3.01  ------ QBF Options
% 19.59/3.01  
% 19.59/3.01  --qbf_mode                              false
% 19.59/3.01  --qbf_elim_univ                         false
% 19.59/3.01  --qbf_dom_inst                          none
% 19.59/3.01  --qbf_dom_pre_inst                      false
% 19.59/3.01  --qbf_sk_in                             false
% 19.59/3.01  --qbf_pred_elim                         true
% 19.59/3.01  --qbf_split                             512
% 19.59/3.01  
% 19.59/3.01  ------ BMC1 Options
% 19.59/3.01  
% 19.59/3.01  --bmc1_incremental                      false
% 19.59/3.01  --bmc1_axioms                           reachable_all
% 19.59/3.01  --bmc1_min_bound                        0
% 19.59/3.01  --bmc1_max_bound                        -1
% 19.59/3.01  --bmc1_max_bound_default                -1
% 19.59/3.01  --bmc1_symbol_reachability              true
% 19.59/3.01  --bmc1_property_lemmas                  false
% 19.59/3.01  --bmc1_k_induction                      false
% 19.59/3.01  --bmc1_non_equiv_states                 false
% 19.59/3.01  --bmc1_deadlock                         false
% 19.59/3.01  --bmc1_ucm                              false
% 19.59/3.01  --bmc1_add_unsat_core                   none
% 19.59/3.01  --bmc1_unsat_core_children              false
% 19.59/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.59/3.01  --bmc1_out_stat                         full
% 19.59/3.01  --bmc1_ground_init                      false
% 19.59/3.01  --bmc1_pre_inst_next_state              false
% 19.59/3.01  --bmc1_pre_inst_state                   false
% 19.59/3.01  --bmc1_pre_inst_reach_state             false
% 19.59/3.01  --bmc1_out_unsat_core                   false
% 19.59/3.01  --bmc1_aig_witness_out                  false
% 19.59/3.01  --bmc1_verbose                          false
% 19.59/3.01  --bmc1_dump_clauses_tptp                false
% 19.59/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.59/3.01  --bmc1_dump_file                        -
% 19.59/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.59/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.59/3.01  --bmc1_ucm_extend_mode                  1
% 19.59/3.01  --bmc1_ucm_init_mode                    2
% 19.59/3.01  --bmc1_ucm_cone_mode                    none
% 19.59/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.59/3.01  --bmc1_ucm_relax_model                  4
% 19.59/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.59/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.59/3.01  --bmc1_ucm_layered_model                none
% 19.59/3.01  --bmc1_ucm_max_lemma_size               10
% 19.59/3.01  
% 19.59/3.01  ------ AIG Options
% 19.59/3.01  
% 19.59/3.01  --aig_mode                              false
% 19.59/3.01  
% 19.59/3.01  ------ Instantiation Options
% 19.59/3.01  
% 19.59/3.01  --instantiation_flag                    true
% 19.59/3.01  --inst_sos_flag                         true
% 19.59/3.01  --inst_sos_phase                        true
% 19.59/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.59/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.59/3.01  --inst_lit_sel_side                     none
% 19.59/3.01  --inst_solver_per_active                1400
% 19.59/3.01  --inst_solver_calls_frac                1.
% 19.59/3.01  --inst_passive_queue_type               priority_queues
% 19.59/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.59/3.01  --inst_passive_queues_freq              [25;2]
% 19.59/3.01  --inst_dismatching                      true
% 19.59/3.01  --inst_eager_unprocessed_to_passive     true
% 19.59/3.01  --inst_prop_sim_given                   true
% 19.59/3.01  --inst_prop_sim_new                     false
% 19.59/3.01  --inst_subs_new                         false
% 19.59/3.01  --inst_eq_res_simp                      false
% 19.59/3.01  --inst_subs_given                       false
% 19.59/3.01  --inst_orphan_elimination               true
% 19.59/3.01  --inst_learning_loop_flag               true
% 19.59/3.01  --inst_learning_start                   3000
% 19.59/3.01  --inst_learning_factor                  2
% 19.59/3.01  --inst_start_prop_sim_after_learn       3
% 19.59/3.01  --inst_sel_renew                        solver
% 19.59/3.01  --inst_lit_activity_flag                true
% 19.59/3.01  --inst_restr_to_given                   false
% 19.59/3.01  --inst_activity_threshold               500
% 19.59/3.01  --inst_out_proof                        true
% 19.59/3.01  
% 19.59/3.01  ------ Resolution Options
% 19.59/3.01  
% 19.59/3.01  --resolution_flag                       false
% 19.59/3.01  --res_lit_sel                           adaptive
% 19.59/3.01  --res_lit_sel_side                      none
% 19.59/3.01  --res_ordering                          kbo
% 19.59/3.01  --res_to_prop_solver                    active
% 19.59/3.01  --res_prop_simpl_new                    false
% 19.59/3.01  --res_prop_simpl_given                  true
% 19.59/3.01  --res_passive_queue_type                priority_queues
% 19.59/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.59/3.01  --res_passive_queues_freq               [15;5]
% 19.59/3.01  --res_forward_subs                      full
% 19.59/3.01  --res_backward_subs                     full
% 19.59/3.01  --res_forward_subs_resolution           true
% 19.59/3.01  --res_backward_subs_resolution          true
% 19.59/3.01  --res_orphan_elimination                true
% 19.59/3.01  --res_time_limit                        2.
% 19.59/3.01  --res_out_proof                         true
% 19.59/3.01  
% 19.59/3.01  ------ Superposition Options
% 19.59/3.01  
% 19.59/3.01  --superposition_flag                    true
% 19.59/3.01  --sup_passive_queue_type                priority_queues
% 19.59/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.59/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.59/3.01  --demod_completeness_check              fast
% 19.59/3.01  --demod_use_ground                      true
% 19.59/3.01  --sup_to_prop_solver                    passive
% 19.59/3.01  --sup_prop_simpl_new                    true
% 19.59/3.01  --sup_prop_simpl_given                  true
% 19.59/3.01  --sup_fun_splitting                     true
% 19.59/3.01  --sup_smt_interval                      50000
% 19.59/3.01  
% 19.59/3.01  ------ Superposition Simplification Setup
% 19.59/3.01  
% 19.59/3.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.59/3.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.59/3.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.59/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.59/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.59/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.59/3.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.59/3.01  --sup_immed_triv                        [TrivRules]
% 19.59/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.59/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.59/3.01  --sup_immed_bw_main                     []
% 19.59/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.59/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.59/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.59/3.01  --sup_input_bw                          []
% 19.59/3.01  
% 19.59/3.01  ------ Combination Options
% 19.59/3.01  
% 19.59/3.01  --comb_res_mult                         3
% 19.59/3.01  --comb_sup_mult                         2
% 19.59/3.01  --comb_inst_mult                        10
% 19.59/3.01  
% 19.59/3.01  ------ Debug Options
% 19.59/3.01  
% 19.59/3.01  --dbg_backtrace                         false
% 19.59/3.01  --dbg_dump_prop_clauses                 false
% 19.59/3.01  --dbg_dump_prop_clauses_file            -
% 19.59/3.01  --dbg_out_stat                          false
% 19.59/3.01  
% 19.59/3.01  
% 19.59/3.01  
% 19.59/3.01  
% 19.59/3.01  ------ Proving...
% 19.59/3.01  
% 19.59/3.01  
% 19.59/3.01  % SZS status Theorem for theBenchmark.p
% 19.59/3.01  
% 19.59/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.59/3.01  
% 19.59/3.01  fof(f1,axiom,(
% 19.59/3.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f30,plain,(
% 19.59/3.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 19.59/3.01    inference(nnf_transformation,[],[f1])).
% 19.59/3.01  
% 19.59/3.01  fof(f31,plain,(
% 19.59/3.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 19.59/3.01    inference(rectify,[],[f30])).
% 19.59/3.01  
% 19.59/3.01  fof(f32,plain,(
% 19.59/3.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 19.59/3.01    introduced(choice_axiom,[])).
% 19.59/3.01  
% 19.59/3.01  fof(f33,plain,(
% 19.59/3.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 19.59/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 19.59/3.01  
% 19.59/3.01  fof(f62,plain,(
% 19.59/3.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f33])).
% 19.59/3.01  
% 19.59/3.01  fof(f12,conjecture,(
% 19.59/3.01    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f13,negated_conjecture,(
% 19.59/3.01    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 19.59/3.01    inference(negated_conjecture,[],[f12])).
% 19.59/3.01  
% 19.59/3.01  fof(f27,plain,(
% 19.59/3.01    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 19.59/3.01    inference(ennf_transformation,[],[f13])).
% 19.59/3.01  
% 19.59/3.01  fof(f59,plain,(
% 19.59/3.01    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) | ~v1_funct_2(sK16,sK14,sK15) | ~v1_funct_1(sK16)) & r2_hidden(sK16,k1_funct_2(sK14,sK15)))),
% 19.59/3.01    introduced(choice_axiom,[])).
% 19.59/3.01  
% 19.59/3.01  fof(f60,plain,(
% 19.59/3.01    (~m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) | ~v1_funct_2(sK16,sK14,sK15) | ~v1_funct_1(sK16)) & r2_hidden(sK16,k1_funct_2(sK14,sK15))),
% 19.59/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f27,f59])).
% 19.59/3.01  
% 19.59/3.01  fof(f103,plain,(
% 19.59/3.01    r2_hidden(sK16,k1_funct_2(sK14,sK15))),
% 19.59/3.01    inference(cnf_transformation,[],[f60])).
% 19.59/3.01  
% 19.59/3.01  fof(f10,axiom,(
% 19.59/3.01    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f28,plain,(
% 19.59/3.01    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 19.59/3.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 19.59/3.01  
% 19.59/3.01  fof(f29,plain,(
% 19.59/3.01    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 19.59/3.01    inference(definition_folding,[],[f10,f28])).
% 19.59/3.01  
% 19.59/3.01  fof(f58,plain,(
% 19.59/3.01    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 19.59/3.01    inference(nnf_transformation,[],[f29])).
% 19.59/3.01  
% 19.59/3.01  fof(f98,plain,(
% 19.59/3.01    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 19.59/3.01    inference(cnf_transformation,[],[f58])).
% 19.59/3.01  
% 19.59/3.01  fof(f116,plain,(
% 19.59/3.01    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 19.59/3.01    inference(equality_resolution,[],[f98])).
% 19.59/3.01  
% 19.59/3.01  fof(f52,plain,(
% 19.59/3.01    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 19.59/3.01    inference(nnf_transformation,[],[f28])).
% 19.59/3.01  
% 19.59/3.01  fof(f53,plain,(
% 19.59/3.01    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 19.59/3.01    inference(rectify,[],[f52])).
% 19.59/3.01  
% 19.59/3.01  fof(f56,plain,(
% 19.59/3.01    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK13(X0,X1,X6)),X0) & k1_relat_1(sK13(X0,X1,X6)) = X1 & sK13(X0,X1,X6) = X6 & v1_funct_1(sK13(X0,X1,X6)) & v1_relat_1(sK13(X0,X1,X6))))),
% 19.59/3.01    introduced(choice_axiom,[])).
% 19.59/3.01  
% 19.59/3.01  fof(f55,plain,(
% 19.59/3.01    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK12(X0,X1,X2)),X0) & k1_relat_1(sK12(X0,X1,X2)) = X1 & sK12(X0,X1,X2) = X3 & v1_funct_1(sK12(X0,X1,X2)) & v1_relat_1(sK12(X0,X1,X2))))) )),
% 19.59/3.01    introduced(choice_axiom,[])).
% 19.59/3.01  
% 19.59/3.01  fof(f54,plain,(
% 19.59/3.01    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK11(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK11(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK11(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK11(X0,X1,X2),X2))))),
% 19.59/3.01    introduced(choice_axiom,[])).
% 19.59/3.01  
% 19.59/3.01  fof(f57,plain,(
% 19.59/3.01    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK11(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK11(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK12(X0,X1,X2)),X0) & k1_relat_1(sK12(X0,X1,X2)) = X1 & sK11(X0,X1,X2) = sK12(X0,X1,X2) & v1_funct_1(sK12(X0,X1,X2)) & v1_relat_1(sK12(X0,X1,X2))) | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK13(X0,X1,X6)),X0) & k1_relat_1(sK13(X0,X1,X6)) = X1 & sK13(X0,X1,X6) = X6 & v1_funct_1(sK13(X0,X1,X6)) & v1_relat_1(sK13(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 19.59/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f53,f56,f55,f54])).
% 19.59/3.01  
% 19.59/3.01  fof(f89,plain,(
% 19.59/3.01    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK13(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f57])).
% 19.59/3.01  
% 19.59/3.01  fof(f88,plain,(
% 19.59/3.01    ( ! [X6,X2,X0,X1] : (sK13(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f57])).
% 19.59/3.01  
% 19.59/3.01  fof(f4,axiom,(
% 19.59/3.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f14,plain,(
% 19.59/3.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.59/3.01    inference(ennf_transformation,[],[f4])).
% 19.59/3.01  
% 19.59/3.01  fof(f15,plain,(
% 19.59/3.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.59/3.01    inference(flattening,[],[f14])).
% 19.59/3.01  
% 19.59/3.01  fof(f42,plain,(
% 19.59/3.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.59/3.01    inference(nnf_transformation,[],[f15])).
% 19.59/3.01  
% 19.59/3.01  fof(f43,plain,(
% 19.59/3.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.59/3.01    inference(rectify,[],[f42])).
% 19.59/3.01  
% 19.59/3.01  fof(f46,plain,(
% 19.59/3.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))))),
% 19.59/3.01    introduced(choice_axiom,[])).
% 19.59/3.01  
% 19.59/3.01  fof(f45,plain,(
% 19.59/3.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X1)) = X2 & r2_hidden(sK6(X0,X1),k1_relat_1(X0))))) )),
% 19.59/3.01    introduced(choice_axiom,[])).
% 19.59/3.01  
% 19.59/3.01  fof(f44,plain,(
% 19.59/3.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1))))),
% 19.59/3.01    introduced(choice_axiom,[])).
% 19.59/3.01  
% 19.59/3.01  fof(f47,plain,(
% 19.59/3.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & ((k1_funct_1(X0,sK6(X0,X1)) = sK5(X0,X1) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.59/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f43,f46,f45,f44])).
% 19.59/3.01  
% 19.59/3.01  fof(f72,plain,(
% 19.59/3.01    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f47])).
% 19.59/3.01  
% 19.59/3.01  fof(f109,plain,(
% 19.59/3.01    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.59/3.01    inference(equality_resolution,[],[f72])).
% 19.59/3.01  
% 19.59/3.01  fof(f110,plain,(
% 19.59/3.01    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.59/3.01    inference(equality_resolution,[],[f109])).
% 19.59/3.01  
% 19.59/3.01  fof(f61,plain,(
% 19.59/3.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f33])).
% 19.59/3.01  
% 19.59/3.01  fof(f86,plain,(
% 19.59/3.01    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK13(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f57])).
% 19.59/3.01  
% 19.59/3.01  fof(f87,plain,(
% 19.59/3.01    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK13(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f57])).
% 19.59/3.01  
% 19.59/3.01  fof(f6,axiom,(
% 19.59/3.01    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f18,plain,(
% 19.59/3.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 19.59/3.01    inference(ennf_transformation,[],[f6])).
% 19.59/3.01  
% 19.59/3.01  fof(f19,plain,(
% 19.59/3.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 19.59/3.01    inference(flattening,[],[f18])).
% 19.59/3.01  
% 19.59/3.01  fof(f80,plain,(
% 19.59/3.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f19])).
% 19.59/3.01  
% 19.59/3.01  fof(f9,axiom,(
% 19.59/3.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f23,plain,(
% 19.59/3.01    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 19.59/3.01    inference(ennf_transformation,[],[f9])).
% 19.59/3.01  
% 19.59/3.01  fof(f24,plain,(
% 19.59/3.01    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 19.59/3.01    inference(flattening,[],[f23])).
% 19.59/3.01  
% 19.59/3.01  fof(f85,plain,(
% 19.59/3.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f24])).
% 19.59/3.01  
% 19.59/3.01  fof(f11,axiom,(
% 19.59/3.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f25,plain,(
% 19.59/3.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.59/3.01    inference(ennf_transformation,[],[f11])).
% 19.59/3.01  
% 19.59/3.01  fof(f26,plain,(
% 19.59/3.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.59/3.01    inference(flattening,[],[f25])).
% 19.59/3.01  
% 19.59/3.01  fof(f101,plain,(
% 19.59/3.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f26])).
% 19.59/3.01  
% 19.59/3.01  fof(f102,plain,(
% 19.59/3.01    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f26])).
% 19.59/3.01  
% 19.59/3.01  fof(f7,axiom,(
% 19.59/3.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f20,plain,(
% 19.59/3.01    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.59/3.01    inference(ennf_transformation,[],[f7])).
% 19.59/3.01  
% 19.59/3.01  fof(f21,plain,(
% 19.59/3.01    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.59/3.01    inference(flattening,[],[f20])).
% 19.59/3.01  
% 19.59/3.01  fof(f82,plain,(
% 19.59/3.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.59/3.01    inference(cnf_transformation,[],[f21])).
% 19.59/3.01  
% 19.59/3.01  fof(f104,plain,(
% 19.59/3.01    ~m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) | ~v1_funct_2(sK16,sK14,sK15) | ~v1_funct_1(sK16)),
% 19.59/3.01    inference(cnf_transformation,[],[f60])).
% 19.59/3.01  
% 19.59/3.01  fof(f2,axiom,(
% 19.59/3.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f34,plain,(
% 19.59/3.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.59/3.01    inference(nnf_transformation,[],[f2])).
% 19.59/3.01  
% 19.59/3.01  fof(f35,plain,(
% 19.59/3.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.59/3.01    inference(flattening,[],[f34])).
% 19.59/3.01  
% 19.59/3.01  fof(f63,plain,(
% 19.59/3.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.59/3.01    inference(cnf_transformation,[],[f35])).
% 19.59/3.01  
% 19.59/3.01  fof(f106,plain,(
% 19.59/3.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.59/3.01    inference(equality_resolution,[],[f63])).
% 19.59/3.01  
% 19.59/3.01  fof(f90,plain,(
% 19.59/3.01    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK13(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f57])).
% 19.59/3.01  
% 19.59/3.01  fof(f8,axiom,(
% 19.59/3.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 19.59/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.59/3.01  
% 19.59/3.01  fof(f22,plain,(
% 19.59/3.01    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 19.59/3.01    inference(ennf_transformation,[],[f8])).
% 19.59/3.01  
% 19.59/3.01  fof(f83,plain,(
% 19.59/3.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 19.59/3.01    inference(cnf_transformation,[],[f22])).
% 19.59/3.01  
% 19.59/3.01  cnf(c_0,plain,
% 19.59/3.01      ( r2_hidden(sK1(X0),X0) | v1_xboole_0(X0) ),
% 19.59/3.01      inference(cnf_transformation,[],[f62]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8576,plain,
% 19.59/3.01      ( r2_hidden(sK1(X0),X0) = iProver_top
% 19.59/3.01      | v1_xboole_0(X0) = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_43,negated_conjecture,
% 19.59/3.01      ( r2_hidden(sK16,k1_funct_2(sK14,sK15)) ),
% 19.59/3.01      inference(cnf_transformation,[],[f103]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8542,plain,
% 19.59/3.01      ( r2_hidden(sK16,k1_funct_2(sK14,sK15)) = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_38,plain,
% 19.59/3.01      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 19.59/3.01      inference(cnf_transformation,[],[f116]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8544,plain,
% 19.59/3.01      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_33,plain,
% 19.59/3.01      ( ~ sP0(X0,X1,X2)
% 19.59/3.01      | ~ r2_hidden(X3,X2)
% 19.59/3.01      | k1_relat_1(sK13(X0,X1,X3)) = X1 ),
% 19.59/3.01      inference(cnf_transformation,[],[f89]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8549,plain,
% 19.59/3.01      ( k1_relat_1(sK13(X0,X1,X2)) = X1
% 19.59/3.01      | sP0(X0,X1,X3) != iProver_top
% 19.59/3.01      | r2_hidden(X2,X3) != iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_10566,plain,
% 19.59/3.01      ( k1_relat_1(sK13(X0,X1,X2)) = X1
% 19.59/3.01      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8544,c_8549]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11642,plain,
% 19.59/3.01      ( k1_relat_1(sK13(sK15,sK14,sK16)) = sK14 ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8542,c_10566]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_34,plain,
% 19.59/3.01      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK13(X0,X1,X3) = X3 ),
% 19.59/3.01      inference(cnf_transformation,[],[f88]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8548,plain,
% 19.59/3.01      ( sK13(X0,X1,X2) = X2
% 19.59/3.01      | sP0(X0,X1,X3) != iProver_top
% 19.59/3.01      | r2_hidden(X2,X3) != iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_9834,plain,
% 19.59/3.01      ( sK13(X0,X1,X2) = X2
% 19.59/3.01      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8544,c_8548]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_10087,plain,
% 19.59/3.01      ( sK13(sK15,sK14,sK16) = sK16 ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8542,c_9834]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11643,plain,
% 19.59/3.01      ( k1_relat_1(sK16) = sK14 ),
% 19.59/3.01      inference(light_normalisation,[status(thm)],[c_11642,c_10087]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_12,plain,
% 19.59/3.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.59/3.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 19.59/3.01      | ~ v1_relat_1(X1)
% 19.59/3.01      | ~ v1_funct_1(X1) ),
% 19.59/3.01      inference(cnf_transformation,[],[f110]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8565,plain,
% 19.59/3.01      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 19.59/3.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 19.59/3.01      | v1_relat_1(X1) != iProver_top
% 19.59/3.01      | v1_funct_1(X1) != iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_1,plain,
% 19.59/3.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 19.59/3.01      inference(cnf_transformation,[],[f61]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8575,plain,
% 19.59/3.01      ( r2_hidden(X0,X1) != iProver_top
% 19.59/3.01      | v1_xboole_0(X1) != iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_12684,plain,
% 19.59/3.01      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 19.59/3.01      | v1_relat_1(X1) != iProver_top
% 19.59/3.01      | v1_funct_1(X1) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8565,c_8575]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_62359,plain,
% 19.59/3.01      ( r2_hidden(X0,sK14) != iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_funct_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16)) != iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_11643,c_12684]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_44,plain,
% 19.59/3.01      ( r2_hidden(sK16,k1_funct_2(sK14,sK15)) = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_36,plain,
% 19.59/3.01      ( ~ sP0(X0,X1,X2)
% 19.59/3.01      | ~ r2_hidden(X3,X2)
% 19.59/3.01      | v1_relat_1(sK13(X0,X1,X3)) ),
% 19.59/3.01      inference(cnf_transformation,[],[f86]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8546,plain,
% 19.59/3.01      ( sP0(X0,X1,X2) != iProver_top
% 19.59/3.01      | r2_hidden(X3,X2) != iProver_top
% 19.59/3.01      | v1_relat_1(sK13(X0,X1,X3)) = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_9681,plain,
% 19.59/3.01      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 19.59/3.01      | v1_relat_1(sK13(X2,X1,X0)) = iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8544,c_8546]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_10942,plain,
% 19.59/3.01      ( v1_relat_1(sK13(sK15,sK14,sK16)) = iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8542,c_9681]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_10943,plain,
% 19.59/3.01      ( v1_relat_1(sK16) = iProver_top ),
% 19.59/3.01      inference(light_normalisation,[status(thm)],[c_10942,c_10087]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_35,plain,
% 19.59/3.01      ( ~ sP0(X0,X1,X2)
% 19.59/3.01      | ~ r2_hidden(X3,X2)
% 19.59/3.01      | v1_funct_1(sK13(X0,X1,X3)) ),
% 19.59/3.01      inference(cnf_transformation,[],[f87]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8547,plain,
% 19.59/3.01      ( sP0(X0,X1,X2) != iProver_top
% 19.59/3.01      | r2_hidden(X3,X2) != iProver_top
% 19.59/3.01      | v1_funct_1(sK13(X0,X1,X3)) = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_9873,plain,
% 19.59/3.01      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 19.59/3.01      | v1_funct_1(sK13(X2,X1,X0)) = iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8544,c_8547]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11036,plain,
% 19.59/3.01      ( v1_funct_1(sK13(sK15,sK14,sK16)) = iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8542,c_9873]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11037,plain,
% 19.59/3.01      ( v1_funct_1(sK16) = iProver_top ),
% 19.59/3.01      inference(light_normalisation,[status(thm)],[c_11036,c_10087]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_19,plain,
% 19.59/3.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.59/3.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 19.59/3.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 19.59/3.01      | ~ v1_relat_1(X0) ),
% 19.59/3.01      inference(cnf_transformation,[],[f80]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8558,plain,
% 19.59/3.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 19.59/3.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 19.59/3.01      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 19.59/3.01      | v1_relat_1(X0) != iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_23,plain,
% 19.59/3.01      ( ~ v1_funct_2(X0,X1,X2)
% 19.59/3.01      | v1_partfun1(X0,X1)
% 19.59/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.59/3.01      | ~ v1_funct_1(X0)
% 19.59/3.01      | v1_xboole_0(X2) ),
% 19.59/3.01      inference(cnf_transformation,[],[f85]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_40,plain,
% 19.59/3.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 19.59/3.01      | ~ v1_relat_1(X0)
% 19.59/3.01      | ~ v1_funct_1(X0) ),
% 19.59/3.01      inference(cnf_transformation,[],[f101]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_620,plain,
% 19.59/3.01      ( v1_partfun1(X0,X1)
% 19.59/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.59/3.01      | ~ v1_relat_1(X3)
% 19.59/3.01      | ~ v1_funct_1(X0)
% 19.59/3.01      | ~ v1_funct_1(X3)
% 19.59/3.01      | v1_xboole_0(X2)
% 19.59/3.01      | X3 != X0
% 19.59/3.01      | k1_relat_1(X3) != X1
% 19.59/3.01      | k2_relat_1(X3) != X2 ),
% 19.59/3.01      inference(resolution_lifted,[status(thm)],[c_23,c_40]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_621,plain,
% 19.59/3.01      ( v1_partfun1(X0,k1_relat_1(X0))
% 19.59/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 19.59/3.01      | ~ v1_relat_1(X0)
% 19.59/3.01      | ~ v1_funct_1(X0)
% 19.59/3.01      | v1_xboole_0(k2_relat_1(X0)) ),
% 19.59/3.01      inference(unflattening,[status(thm)],[c_620]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_39,plain,
% 19.59/3.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 19.59/3.01      | ~ v1_relat_1(X0)
% 19.59/3.01      | ~ v1_funct_1(X0) ),
% 19.59/3.01      inference(cnf_transformation,[],[f102]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_625,plain,
% 19.59/3.01      ( v1_partfun1(X0,k1_relat_1(X0))
% 19.59/3.01      | ~ v1_relat_1(X0)
% 19.59/3.01      | ~ v1_funct_1(X0)
% 19.59/3.01      | v1_xboole_0(k2_relat_1(X0)) ),
% 19.59/3.01      inference(global_propositional_subsumption,
% 19.59/3.01                [status(thm)],
% 19.59/3.01                [c_621,c_39]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_20,plain,
% 19.59/3.01      ( v1_funct_2(X0,X1,X2)
% 19.59/3.01      | ~ v1_partfun1(X0,X1)
% 19.59/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.59/3.01      | ~ v1_funct_1(X0) ),
% 19.59/3.01      inference(cnf_transformation,[],[f82]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_42,negated_conjecture,
% 19.59/3.01      ( ~ v1_funct_2(sK16,sK14,sK15)
% 19.59/3.01      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
% 19.59/3.01      | ~ v1_funct_1(sK16) ),
% 19.59/3.01      inference(cnf_transformation,[],[f104]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_644,plain,
% 19.59/3.01      ( ~ v1_partfun1(X0,X1)
% 19.59/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.59/3.01      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
% 19.59/3.01      | ~ v1_funct_1(X0)
% 19.59/3.01      | ~ v1_funct_1(sK16)
% 19.59/3.01      | sK15 != X2
% 19.59/3.01      | sK14 != X1
% 19.59/3.01      | sK16 != X0 ),
% 19.59/3.01      inference(resolution_lifted,[status(thm)],[c_20,c_42]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_645,plain,
% 19.59/3.01      ( ~ v1_partfun1(sK16,sK14)
% 19.59/3.01      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
% 19.59/3.01      | ~ v1_funct_1(sK16) ),
% 19.59/3.01      inference(unflattening,[status(thm)],[c_644]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_709,plain,
% 19.59/3.01      ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
% 19.59/3.01      | ~ v1_relat_1(X0)
% 19.59/3.01      | ~ v1_funct_1(X0)
% 19.59/3.01      | ~ v1_funct_1(sK16)
% 19.59/3.01      | v1_xboole_0(k2_relat_1(X0))
% 19.59/3.01      | k1_relat_1(X0) != sK14
% 19.59/3.01      | sK16 != X0 ),
% 19.59/3.01      inference(resolution_lifted,[status(thm)],[c_625,c_645]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_710,plain,
% 19.59/3.01      ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
% 19.59/3.01      | ~ v1_relat_1(sK16)
% 19.59/3.01      | ~ v1_funct_1(sK16)
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16))
% 19.59/3.01      | k1_relat_1(sK16) != sK14 ),
% 19.59/3.01      inference(unflattening,[status(thm)],[c_709]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8538,plain,
% 19.59/3.01      ( k1_relat_1(sK16) != sK14
% 19.59/3.01      | m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_funct_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11664,plain,
% 19.59/3.01      ( sK14 != sK14
% 19.59/3.01      | m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_funct_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
% 19.59/3.01      inference(demodulation,[status(thm)],[c_11643,c_8538]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11667,plain,
% 19.59/3.01      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_funct_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
% 19.59/3.01      inference(equality_resolution_simp,[status(thm)],[c_11664]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_711,plain,
% 19.59/3.01      ( k1_relat_1(sK16) != sK14
% 19.59/3.01      | m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_funct_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11984,plain,
% 19.59/3.01      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
% 19.59/3.01      inference(global_propositional_subsumption,
% 19.59/3.01                [status(thm)],
% 19.59/3.01                [c_11667,c_711,c_10943,c_11037,c_11643]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_13265,plain,
% 19.59/3.01      ( r1_tarski(k1_relat_1(sK16),sK14) != iProver_top
% 19.59/3.01      | r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8558,c_11984]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_13268,plain,
% 19.59/3.01      ( r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
% 19.59/3.01      | r1_tarski(sK14,sK14) != iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
% 19.59/3.01      inference(light_normalisation,[status(thm)],[c_13265,c_11643]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_4,plain,
% 19.59/3.01      ( r1_tarski(X0,X0) ),
% 19.59/3.01      inference(cnf_transformation,[],[f106]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11627,plain,
% 19.59/3.01      ( r1_tarski(sK14,sK14) ),
% 19.59/3.01      inference(instantiation,[status(thm)],[c_4]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11628,plain,
% 19.59/3.01      ( r1_tarski(sK14,sK14) = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_11627]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_13564,plain,
% 19.59/3.01      ( r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
% 19.59/3.01      | v1_xboole_0(k2_relat_1(sK16)) = iProver_top ),
% 19.59/3.01      inference(global_propositional_subsumption,
% 19.59/3.01                [status(thm)],
% 19.59/3.01                [c_13268,c_10943,c_11628]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_32,plain,
% 19.59/3.01      ( ~ sP0(X0,X1,X2)
% 19.59/3.01      | r1_tarski(k2_relat_1(sK13(X0,X1,X3)),X0)
% 19.59/3.01      | ~ r2_hidden(X3,X2) ),
% 19.59/3.01      inference(cnf_transformation,[],[f90]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8550,plain,
% 19.59/3.01      ( sP0(X0,X1,X2) != iProver_top
% 19.59/3.01      | r1_tarski(k2_relat_1(sK13(X0,X1,X3)),X0) = iProver_top
% 19.59/3.01      | r2_hidden(X3,X2) != iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_10850,plain,
% 19.59/3.01      ( r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X0) = iProver_top
% 19.59/3.01      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8544,c_8550]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_23170,plain,
% 19.59/3.01      ( r1_tarski(k2_relat_1(sK16),sK15) = iProver_top
% 19.59/3.01      | r2_hidden(sK16,k1_funct_2(sK14,sK15)) != iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_10087,c_10850]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_62431,plain,
% 19.59/3.01      ( r2_hidden(X0,sK14) != iProver_top ),
% 19.59/3.01      inference(global_propositional_subsumption,
% 19.59/3.01                [status(thm)],
% 19.59/3.01                [c_62359,c_44,c_10943,c_11037,c_11628,c_13268,c_23170]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_62437,plain,
% 19.59/3.01      ( v1_xboole_0(sK14) = iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8576,c_62431]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_22,plain,
% 19.59/3.01      ( v1_partfun1(X0,X1)
% 19.59/3.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.59/3.01      | ~ v1_xboole_0(X1) ),
% 19.59/3.01      inference(cnf_transformation,[],[f83]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_691,plain,
% 19.59/3.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.59/3.01      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
% 19.59/3.01      | ~ v1_funct_1(sK16)
% 19.59/3.01      | ~ v1_xboole_0(X1)
% 19.59/3.01      | sK14 != X1
% 19.59/3.01      | sK16 != X0 ),
% 19.59/3.01      inference(resolution_lifted,[status(thm)],[c_22,c_645]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_692,plain,
% 19.59/3.01      ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,X0)))
% 19.59/3.01      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
% 19.59/3.01      | ~ v1_funct_1(sK16)
% 19.59/3.01      | ~ v1_xboole_0(sK14) ),
% 19.59/3.01      inference(unflattening,[status(thm)],[c_691]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_7886,plain,
% 19.59/3.01      ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15)))
% 19.59/3.01      | ~ v1_funct_1(sK16)
% 19.59/3.01      | ~ v1_xboole_0(sK14)
% 19.59/3.01      | sP0_iProver_split ),
% 19.59/3.01      inference(splitting,
% 19.59/3.01                [splitting(split),new_symbols(definition,[])],
% 19.59/3.01                [c_692]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8539,plain,
% 19.59/3.01      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,sK15))) != iProver_top
% 19.59/3.01      | v1_funct_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(sK14) != iProver_top
% 19.59/3.01      | sP0_iProver_split = iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_7886]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_13266,plain,
% 19.59/3.01      ( r1_tarski(k1_relat_1(sK16),sK14) != iProver_top
% 19.59/3.01      | r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_funct_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(sK14) != iProver_top
% 19.59/3.01      | sP0_iProver_split = iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_8558,c_8539]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_13267,plain,
% 19.59/3.01      ( r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
% 19.59/3.01      | r1_tarski(sK14,sK14) != iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_funct_1(sK16) != iProver_top
% 19.59/3.01      | v1_xboole_0(sK14) != iProver_top
% 19.59/3.01      | sP0_iProver_split = iProver_top ),
% 19.59/3.01      inference(light_normalisation,[status(thm)],[c_13266,c_11643]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8543,plain,
% 19.59/3.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 19.59/3.01      | v1_relat_1(X0) != iProver_top
% 19.59/3.01      | v1_funct_1(X0) != iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11670,plain,
% 19.59/3.01      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,k2_relat_1(sK16)))) = iProver_top
% 19.59/3.01      | v1_relat_1(sK16) != iProver_top
% 19.59/3.01      | v1_funct_1(sK16) != iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_11643,c_8543]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11768,plain,
% 19.59/3.01      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,k2_relat_1(sK16)))) = iProver_top ),
% 19.59/3.01      inference(global_propositional_subsumption,
% 19.59/3.01                [status(thm)],
% 19.59/3.01                [c_11670,c_10943,c_11037]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_7885,plain,
% 19.59/3.01      ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,X0)))
% 19.59/3.01      | ~ sP0_iProver_split ),
% 19.59/3.01      inference(splitting,
% 19.59/3.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 19.59/3.01                [c_692]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_8540,plain,
% 19.59/3.01      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK14,X0))) != iProver_top
% 19.59/3.01      | sP0_iProver_split != iProver_top ),
% 19.59/3.01      inference(predicate_to_equality,[status(thm)],[c_7885]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_11772,plain,
% 19.59/3.01      ( sP0_iProver_split != iProver_top ),
% 19.59/3.01      inference(superposition,[status(thm)],[c_11768,c_8540]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_13569,plain,
% 19.59/3.01      ( v1_xboole_0(sK14) != iProver_top
% 19.59/3.01      | r1_tarski(k2_relat_1(sK16),sK15) != iProver_top ),
% 19.59/3.01      inference(global_propositional_subsumption,
% 19.59/3.01                [status(thm)],
% 19.59/3.01                [c_13267,c_10943,c_11037,c_11628,c_11772]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(c_13570,plain,
% 19.59/3.01      ( r1_tarski(k2_relat_1(sK16),sK15) != iProver_top
% 19.59/3.01      | v1_xboole_0(sK14) != iProver_top ),
% 19.59/3.01      inference(renaming,[status(thm)],[c_13569]) ).
% 19.59/3.01  
% 19.59/3.01  cnf(contradiction,plain,
% 19.59/3.01      ( $false ),
% 19.59/3.01      inference(minisat,[status(thm)],[c_62437,c_23170,c_13570,c_44]) ).
% 19.59/3.01  
% 19.59/3.01  
% 19.59/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.59/3.01  
% 19.59/3.01  ------                               Statistics
% 19.59/3.01  
% 19.59/3.01  ------ General
% 19.59/3.01  
% 19.59/3.01  abstr_ref_over_cycles:                  0
% 19.59/3.01  abstr_ref_under_cycles:                 0
% 19.59/3.01  gc_basic_clause_elim:                   0
% 19.59/3.01  forced_gc_time:                         0
% 19.59/3.01  parsing_time:                           0.01
% 19.59/3.01  unif_index_cands_time:                  0.
% 19.59/3.01  unif_index_add_time:                    0.
% 19.59/3.01  orderings_time:                         0.
% 19.59/3.01  out_proof_time:                         0.017
% 19.59/3.01  total_time:                             2.133
% 19.59/3.01  num_of_symbols:                         64
% 19.59/3.01  num_of_terms:                           86957
% 19.59/3.01  
% 19.59/3.01  ------ Preprocessing
% 19.59/3.01  
% 19.59/3.01  num_of_splits:                          1
% 19.59/3.01  num_of_split_atoms:                     1
% 19.59/3.01  num_of_reused_defs:                     0
% 19.59/3.01  num_eq_ax_congr_red:                    84
% 19.59/3.01  num_of_sem_filtered_clauses:            1
% 19.59/3.01  num_of_subtypes:                        0
% 19.59/3.01  monotx_restored_types:                  0
% 19.59/3.01  sat_num_of_epr_types:                   0
% 19.59/3.01  sat_num_of_non_cyclic_types:            0
% 19.59/3.01  sat_guarded_non_collapsed_types:        0
% 19.59/3.01  num_pure_diseq_elim:                    0
% 19.59/3.01  simp_replaced_by:                       0
% 19.59/3.01  res_preprocessed:                       191
% 19.59/3.01  prep_upred:                             0
% 19.59/3.01  prep_unflattend:                        268
% 19.59/3.01  smt_new_axioms:                         0
% 19.59/3.01  pred_elim_cands:                        7
% 19.59/3.01  pred_elim:                              2
% 19.59/3.01  pred_elim_cl:                           2
% 19.59/3.01  pred_elim_cycles:                       12
% 19.59/3.01  merged_defs:                            0
% 19.59/3.01  merged_defs_ncl:                        0
% 19.59/3.01  bin_hyper_res:                          0
% 19.59/3.01  prep_cycles:                            4
% 19.59/3.01  pred_elim_time:                         0.101
% 19.59/3.01  splitting_time:                         0.
% 19.59/3.01  sem_filter_time:                        0.
% 19.59/3.01  monotx_time:                            0.
% 19.59/3.01  subtype_inf_time:                       0.
% 19.59/3.01  
% 19.59/3.01  ------ Problem properties
% 19.59/3.01  
% 19.59/3.01  clauses:                                39
% 19.59/3.01  conjectures:                            1
% 19.59/3.01  epr:                                    3
% 19.59/3.01  horn:                                   28
% 19.59/3.01  ground:                                 4
% 19.59/3.01  unary:                                  3
% 19.59/3.01  binary:                                 9
% 19.59/3.01  lits:                                   124
% 19.59/3.01  lits_eq:                                20
% 19.59/3.01  fd_pure:                                0
% 19.59/3.01  fd_pseudo:                              0
% 19.59/3.01  fd_cond:                                0
% 19.59/3.01  fd_pseudo_cond:                         8
% 19.59/3.01  ac_symbols:                             0
% 19.59/3.01  
% 19.59/3.01  ------ Propositional Solver
% 19.59/3.01  
% 19.59/3.01  prop_solver_calls:                      35
% 19.59/3.01  prop_fast_solver_calls:                 4399
% 19.59/3.01  smt_solver_calls:                       0
% 19.59/3.01  smt_fast_solver_calls:                  0
% 19.59/3.01  prop_num_of_clauses:                    27577
% 19.59/3.01  prop_preprocess_simplified:             45038
% 19.59/3.01  prop_fo_subsumed:                       240
% 19.59/3.01  prop_solver_time:                       0.
% 19.59/3.01  smt_solver_time:                        0.
% 19.59/3.01  smt_fast_solver_time:                   0.
% 19.59/3.01  prop_fast_solver_time:                  0.
% 19.59/3.01  prop_unsat_core_time:                   0.002
% 19.59/3.01  
% 19.59/3.01  ------ QBF
% 19.59/3.01  
% 19.59/3.01  qbf_q_res:                              0
% 19.59/3.01  qbf_num_tautologies:                    0
% 19.59/3.01  qbf_prep_cycles:                        0
% 19.59/3.01  
% 19.59/3.01  ------ BMC1
% 19.59/3.01  
% 19.59/3.01  bmc1_current_bound:                     -1
% 19.59/3.01  bmc1_last_solved_bound:                 -1
% 19.59/3.01  bmc1_unsat_core_size:                   -1
% 19.59/3.01  bmc1_unsat_core_parents_size:           -1
% 19.59/3.01  bmc1_merge_next_fun:                    0
% 19.59/3.01  bmc1_unsat_core_clauses_time:           0.
% 19.59/3.01  
% 19.59/3.01  ------ Instantiation
% 19.59/3.01  
% 19.59/3.01  inst_num_of_clauses:                    4705
% 19.59/3.01  inst_num_in_passive:                    3010
% 19.59/3.01  inst_num_in_active:                     1568
% 19.59/3.01  inst_num_in_unprocessed:                128
% 19.59/3.01  inst_num_of_loops:                      1990
% 19.59/3.01  inst_num_of_learning_restarts:          0
% 19.59/3.01  inst_num_moves_active_passive:          418
% 19.59/3.01  inst_lit_activity:                      0
% 19.59/3.01  inst_lit_activity_moves:                0
% 19.59/3.01  inst_num_tautologies:                   0
% 19.59/3.01  inst_num_prop_implied:                  0
% 19.59/3.01  inst_num_existing_simplified:           0
% 19.59/3.01  inst_num_eq_res_simplified:             0
% 19.59/3.01  inst_num_child_elim:                    0
% 19.59/3.01  inst_num_of_dismatching_blockings:      6776
% 19.59/3.01  inst_num_of_non_proper_insts:           5707
% 19.59/3.01  inst_num_of_duplicates:                 0
% 19.59/3.01  inst_inst_num_from_inst_to_res:         0
% 19.59/3.01  inst_dismatching_checking_time:         0.
% 19.59/3.01  
% 19.59/3.01  ------ Resolution
% 19.59/3.01  
% 19.59/3.01  res_num_of_clauses:                     0
% 19.59/3.01  res_num_in_passive:                     0
% 19.59/3.01  res_num_in_active:                      0
% 19.59/3.01  res_num_of_loops:                       195
% 19.59/3.01  res_forward_subset_subsumed:            166
% 19.59/3.01  res_backward_subset_subsumed:           2
% 19.59/3.01  res_forward_subsumed:                   0
% 19.59/3.01  res_backward_subsumed:                  0
% 19.59/3.01  res_forward_subsumption_resolution:     2
% 19.59/3.01  res_backward_subsumption_resolution:    0
% 19.59/3.01  res_clause_to_clause_subsumption:       12513
% 19.59/3.01  res_orphan_elimination:                 0
% 19.59/3.01  res_tautology_del:                      286
% 19.59/3.01  res_num_eq_res_simplified:              0
% 19.59/3.01  res_num_sel_changes:                    0
% 19.59/3.01  res_moves_from_active_to_pass:          0
% 19.59/3.01  
% 19.59/3.01  ------ Superposition
% 19.59/3.01  
% 19.59/3.01  sup_time_total:                         0.
% 19.59/3.01  sup_time_generating:                    0.
% 19.59/3.01  sup_time_sim_full:                      0.
% 19.59/3.01  sup_time_sim_immed:                     0.
% 19.59/3.01  
% 19.59/3.01  sup_num_of_clauses:                     3124
% 19.59/3.01  sup_num_in_active:                      310
% 19.59/3.01  sup_num_in_passive:                     2814
% 19.59/3.01  sup_num_of_loops:                       397
% 19.59/3.01  sup_fw_superposition:                   3238
% 19.59/3.01  sup_bw_superposition:                   1026
% 19.59/3.01  sup_immediate_simplified:               694
% 19.59/3.01  sup_given_eliminated:                   1
% 19.59/3.01  comparisons_done:                       0
% 19.59/3.01  comparisons_avoided:                    54
% 19.59/3.01  
% 19.59/3.01  ------ Simplifications
% 19.59/3.01  
% 19.59/3.01  
% 19.59/3.01  sim_fw_subset_subsumed:                 221
% 19.59/3.01  sim_bw_subset_subsumed:                 21
% 19.59/3.01  sim_fw_subsumed:                        247
% 19.59/3.01  sim_bw_subsumed:                        144
% 19.59/3.01  sim_fw_subsumption_res:                 0
% 19.59/3.01  sim_bw_subsumption_res:                 0
% 19.59/3.01  sim_tautology_del:                      23
% 19.59/3.01  sim_eq_tautology_del:                   68
% 19.59/3.01  sim_eq_res_simp:                        2
% 19.59/3.01  sim_fw_demodulated:                     31
% 19.59/3.01  sim_bw_demodulated:                     2
% 19.59/3.01  sim_light_normalised:                   195
% 19.59/3.01  sim_joinable_taut:                      0
% 19.59/3.01  sim_joinable_simp:                      0
% 19.59/3.01  sim_ac_normalised:                      0
% 19.59/3.01  sim_smt_subsumption:                    0
% 19.59/3.01  
%------------------------------------------------------------------------------

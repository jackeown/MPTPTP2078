%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:14 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 941 expanded)
%              Number of clauses        :   79 ( 302 expanded)
%              Number of leaves         :   16 ( 242 expanded)
%              Depth                    :   19
%              Number of atoms          :  580 (5943 expanded)
%              Number of equality atoms :  200 (1780 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
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

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f7,f24])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,
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

fof(f40,plain,
    ( ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7) )
    & r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f23,f39])).

fof(f70,plain,(
    r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f40])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).

fof(f55,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK4(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ! [X6,X2,X0,X1] :
      ( sK4(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | k1_relat_1(X7) != X1
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X6,X2,X0,X7] :
      ( r2_hidden(X6,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | X6 != X7
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP0(X0,k1_relat_1(X7),X2) ) ),
    inference(equality_resolution,[],[f57])).

fof(f76,plain,(
    ! [X2,X0,X7] :
      ( r2_hidden(X7,X2)
      | ~ r1_tarski(k2_relat_1(X7),X0)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | ~ sP0(X0,k1_relat_1(X7),X2) ) ),
    inference(equality_resolution,[],[f75])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_25,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_7047,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7048,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7063,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7045,plain,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK4(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7053,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8031,plain,
    ( k1_relat_1(sK4(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7048,c_7053])).

cnf(c_8365,plain,
    ( k1_relat_1(sK4(sK6,sK5,sK7)) = sK5 ),
    inference(superposition,[status(thm)],[c_7045,c_8031])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK4(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7052,plain,
    ( sK4(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7785,plain,
    ( sK4(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7048,c_7052])).

cnf(c_7869,plain,
    ( sK4(sK6,sK5,sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_7045,c_7785])).

cnf(c_8367,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_8365,c_7869])).

cnf(c_17,plain,
    ( ~ sP0(X0,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X0)
    | r2_hidden(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7055,plain,
    ( sP0(X0,k1_relat_1(X1),X2) != iProver_top
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9882,plain,
    ( sP0(X0,sK5,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK7),X0) != iProver_top
    | r2_hidden(sK7,X1) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8367,c_7055])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7050,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_relat_1(sK4(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7993,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_relat_1(sK4(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7048,c_7050])).

cnf(c_8137,plain,
    ( v1_relat_1(sK4(sK6,sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7045,c_7993])).

cnf(c_8139,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8137,c_7869])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7051,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_funct_1(sK4(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7999,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_funct_1(sK4(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7048,c_7051])).

cnf(c_8265,plain,
    ( v1_funct_1(sK4(sK6,sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7045,c_7999])).

cnf(c_8267,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8265,c_7869])).

cnf(c_10402,plain,
    ( sP0(X0,sK5,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK7),X0) != iProver_top
    | r2_hidden(sK7,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9882,c_8139,c_8267])).

cnf(c_10411,plain,
    ( sP0(k2_relat_1(sK7),sK5,X0) != iProver_top
    | r2_hidden(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7063,c_10402])).

cnf(c_10662,plain,
    ( r2_hidden(sK7,k1_funct_2(sK5,k2_relat_1(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7048,c_10411])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7065,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10666,plain,
    ( v1_xboole_0(k1_funct_2(sK5,k2_relat_1(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10662,c_7065])).

cnf(c_10782,plain,
    ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7047,c_10666])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7054,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8776,plain,
    ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7048,c_7054])).

cnf(c_9613,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top
    | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7869,c_8776])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7062,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_381,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k1_relat_1(X3) != X1
    | k2_relat_1(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_382,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_386,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_26])).

cnf(c_6,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_29,negated_conjecture,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_405,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | sK6 != X2
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_406,plain,
    ( ~ v1_partfun1(sK7,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_470,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK5
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_386,c_406])).

cnf(c_471,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | v1_xboole_0(k2_relat_1(sK7))
    | k1_relat_1(sK7) != sK5 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_7041,plain,
    ( k1_relat_1(sK7) != sK5
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_8576,plain,
    ( sK5 != sK5
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8367,c_7041])).

cnf(c_8587,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8576])).

cnf(c_472,plain,
    ( k1_relat_1(sK7) != sK5
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_9521,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8587,c_472,c_8139,c_8267,c_8367])).

cnf(c_9527,plain,
    ( r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7062,c_9521])).

cnf(c_9528,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9527,c_8367])).

cnf(c_9531,plain,
    ( r1_tarski(sK5,sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9528,c_8139])).

cnf(c_9532,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9531])).

cnf(c_9538,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9532,c_7063])).

cnf(c_8,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_xboole_0(X1)
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_406])).

cnf(c_453,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_6544,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ v1_xboole_0(sK5)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_453])).

cnf(c_7042,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6544])).

cnf(c_6543,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_453])).

cnf(c_7043,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6543])).

cnf(c_7159,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7042,c_7043])).

cnf(c_9189,plain,
    ( r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7062,c_7159])).

cnf(c_9196,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9189,c_8367])).

cnf(c_9351,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9196,c_8139,c_8267])).

cnf(c_9358,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9351,c_7063])).

cnf(c_31,plain,
    ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10782,c_9613,c_9538,c_9358,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.33/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/0.99  
% 3.33/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/0.99  
% 3.33/0.99  ------  iProver source info
% 3.33/0.99  
% 3.33/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.33/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/0.99  git: non_committed_changes: false
% 3.33/0.99  git: last_make_outside_of_git: false
% 3.33/0.99  
% 3.33/0.99  ------ 
% 3.33/0.99  
% 3.33/0.99  ------ Input Options
% 3.33/0.99  
% 3.33/0.99  --out_options                           all
% 3.33/0.99  --tptp_safe_out                         true
% 3.33/0.99  --problem_path                          ""
% 3.33/0.99  --include_path                          ""
% 3.33/0.99  --clausifier                            res/vclausify_rel
% 3.33/0.99  --clausifier_options                    --mode clausify
% 3.33/0.99  --stdin                                 false
% 3.33/0.99  --stats_out                             all
% 3.33/0.99  
% 3.33/0.99  ------ General Options
% 3.33/0.99  
% 3.33/0.99  --fof                                   false
% 3.33/0.99  --time_out_real                         305.
% 3.33/0.99  --time_out_virtual                      -1.
% 3.33/0.99  --symbol_type_check                     false
% 3.33/0.99  --clausify_out                          false
% 3.33/0.99  --sig_cnt_out                           false
% 3.33/0.99  --trig_cnt_out                          false
% 3.33/0.99  --trig_cnt_out_tolerance                1.
% 3.33/0.99  --trig_cnt_out_sk_spl                   false
% 3.33/0.99  --abstr_cl_out                          false
% 3.33/0.99  
% 3.33/0.99  ------ Global Options
% 3.33/0.99  
% 3.33/0.99  --schedule                              default
% 3.33/0.99  --add_important_lit                     false
% 3.33/0.99  --prop_solver_per_cl                    1000
% 3.33/0.99  --min_unsat_core                        false
% 3.33/0.99  --soft_assumptions                      false
% 3.33/0.99  --soft_lemma_size                       3
% 3.33/0.99  --prop_impl_unit_size                   0
% 3.33/0.99  --prop_impl_unit                        []
% 3.33/0.99  --share_sel_clauses                     true
% 3.33/0.99  --reset_solvers                         false
% 3.33/0.99  --bc_imp_inh                            [conj_cone]
% 3.33/0.99  --conj_cone_tolerance                   3.
% 3.33/0.99  --extra_neg_conj                        none
% 3.33/0.99  --large_theory_mode                     true
% 3.33/0.99  --prolific_symb_bound                   200
% 3.33/0.99  --lt_threshold                          2000
% 3.33/0.99  --clause_weak_htbl                      true
% 3.33/0.99  --gc_record_bc_elim                     false
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing Options
% 3.33/0.99  
% 3.33/0.99  --preprocessing_flag                    true
% 3.33/0.99  --time_out_prep_mult                    0.1
% 3.33/0.99  --splitting_mode                        input
% 3.33/0.99  --splitting_grd                         true
% 3.33/0.99  --splitting_cvd                         false
% 3.33/0.99  --splitting_cvd_svl                     false
% 3.33/0.99  --splitting_nvd                         32
% 3.33/0.99  --sub_typing                            true
% 3.33/0.99  --prep_gs_sim                           true
% 3.33/0.99  --prep_unflatten                        true
% 3.33/0.99  --prep_res_sim                          true
% 3.33/0.99  --prep_upred                            true
% 3.33/0.99  --prep_sem_filter                       exhaustive
% 3.33/0.99  --prep_sem_filter_out                   false
% 3.33/0.99  --pred_elim                             true
% 3.33/0.99  --res_sim_input                         true
% 3.33/0.99  --eq_ax_congr_red                       true
% 3.33/0.99  --pure_diseq_elim                       true
% 3.33/0.99  --brand_transform                       false
% 3.33/0.99  --non_eq_to_eq                          false
% 3.33/0.99  --prep_def_merge                        true
% 3.33/0.99  --prep_def_merge_prop_impl              false
% 3.33/0.99  --prep_def_merge_mbd                    true
% 3.33/0.99  --prep_def_merge_tr_red                 false
% 3.33/0.99  --prep_def_merge_tr_cl                  false
% 3.33/0.99  --smt_preprocessing                     true
% 3.33/0.99  --smt_ac_axioms                         fast
% 3.33/0.99  --preprocessed_out                      false
% 3.33/0.99  --preprocessed_stats                    false
% 3.33/0.99  
% 3.33/0.99  ------ Abstraction refinement Options
% 3.33/0.99  
% 3.33/0.99  --abstr_ref                             []
% 3.33/0.99  --abstr_ref_prep                        false
% 3.33/0.99  --abstr_ref_until_sat                   false
% 3.33/0.99  --abstr_ref_sig_restrict                funpre
% 3.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.99  --abstr_ref_under                       []
% 3.33/0.99  
% 3.33/0.99  ------ SAT Options
% 3.33/0.99  
% 3.33/0.99  --sat_mode                              false
% 3.33/0.99  --sat_fm_restart_options                ""
% 3.33/0.99  --sat_gr_def                            false
% 3.33/0.99  --sat_epr_types                         true
% 3.33/0.99  --sat_non_cyclic_types                  false
% 3.33/0.99  --sat_finite_models                     false
% 3.33/0.99  --sat_fm_lemmas                         false
% 3.33/0.99  --sat_fm_prep                           false
% 3.33/0.99  --sat_fm_uc_incr                        true
% 3.33/0.99  --sat_out_model                         small
% 3.33/0.99  --sat_out_clauses                       false
% 3.33/0.99  
% 3.33/0.99  ------ QBF Options
% 3.33/0.99  
% 3.33/0.99  --qbf_mode                              false
% 3.33/0.99  --qbf_elim_univ                         false
% 3.33/0.99  --qbf_dom_inst                          none
% 3.33/0.99  --qbf_dom_pre_inst                      false
% 3.33/0.99  --qbf_sk_in                             false
% 3.33/0.99  --qbf_pred_elim                         true
% 3.33/0.99  --qbf_split                             512
% 3.33/0.99  
% 3.33/0.99  ------ BMC1 Options
% 3.33/0.99  
% 3.33/0.99  --bmc1_incremental                      false
% 3.33/0.99  --bmc1_axioms                           reachable_all
% 3.33/0.99  --bmc1_min_bound                        0
% 3.33/0.99  --bmc1_max_bound                        -1
% 3.33/0.99  --bmc1_max_bound_default                -1
% 3.33/0.99  --bmc1_symbol_reachability              true
% 3.33/0.99  --bmc1_property_lemmas                  false
% 3.33/0.99  --bmc1_k_induction                      false
% 3.33/0.99  --bmc1_non_equiv_states                 false
% 3.33/0.99  --bmc1_deadlock                         false
% 3.33/0.99  --bmc1_ucm                              false
% 3.33/0.99  --bmc1_add_unsat_core                   none
% 3.33/0.99  --bmc1_unsat_core_children              false
% 3.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.99  --bmc1_out_stat                         full
% 3.33/0.99  --bmc1_ground_init                      false
% 3.33/0.99  --bmc1_pre_inst_next_state              false
% 3.33/0.99  --bmc1_pre_inst_state                   false
% 3.33/0.99  --bmc1_pre_inst_reach_state             false
% 3.33/0.99  --bmc1_out_unsat_core                   false
% 3.33/0.99  --bmc1_aig_witness_out                  false
% 3.33/0.99  --bmc1_verbose                          false
% 3.33/0.99  --bmc1_dump_clauses_tptp                false
% 3.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.99  --bmc1_dump_file                        -
% 3.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.99  --bmc1_ucm_extend_mode                  1
% 3.33/0.99  --bmc1_ucm_init_mode                    2
% 3.33/0.99  --bmc1_ucm_cone_mode                    none
% 3.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.33/0.99  --bmc1_ucm_relax_model                  4
% 3.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/0.99  --bmc1_ucm_layered_model                none
% 3.33/0.99  --bmc1_ucm_max_lemma_size               10
% 3.33/0.99  
% 3.33/0.99  ------ AIG Options
% 3.33/0.99  
% 3.33/0.99  --aig_mode                              false
% 3.33/0.99  
% 3.33/0.99  ------ Instantiation Options
% 3.33/0.99  
% 3.33/0.99  --instantiation_flag                    true
% 3.33/0.99  --inst_sos_flag                         false
% 3.33/0.99  --inst_sos_phase                        true
% 3.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/0.99  --inst_lit_sel_side                     num_symb
% 3.33/0.99  --inst_solver_per_active                1400
% 3.33/0.99  --inst_solver_calls_frac                1.
% 3.33/0.99  --inst_passive_queue_type               priority_queues
% 3.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/0.99  --inst_passive_queues_freq              [25;2]
% 3.33/0.99  --inst_dismatching                      true
% 3.33/0.99  --inst_eager_unprocessed_to_passive     true
% 3.33/0.99  --inst_prop_sim_given                   true
% 3.33/0.99  --inst_prop_sim_new                     false
% 3.33/0.99  --inst_subs_new                         false
% 3.33/0.99  --inst_eq_res_simp                      false
% 3.33/0.99  --inst_subs_given                       false
% 3.33/0.99  --inst_orphan_elimination               true
% 3.33/0.99  --inst_learning_loop_flag               true
% 3.33/0.99  --inst_learning_start                   3000
% 3.33/0.99  --inst_learning_factor                  2
% 3.33/0.99  --inst_start_prop_sim_after_learn       3
% 3.33/0.99  --inst_sel_renew                        solver
% 3.33/0.99  --inst_lit_activity_flag                true
% 3.33/0.99  --inst_restr_to_given                   false
% 3.33/0.99  --inst_activity_threshold               500
% 3.33/0.99  --inst_out_proof                        true
% 3.33/0.99  
% 3.33/0.99  ------ Resolution Options
% 3.33/0.99  
% 3.33/0.99  --resolution_flag                       true
% 3.33/0.99  --res_lit_sel                           adaptive
% 3.33/0.99  --res_lit_sel_side                      none
% 3.33/0.99  --res_ordering                          kbo
% 3.33/0.99  --res_to_prop_solver                    active
% 3.33/0.99  --res_prop_simpl_new                    false
% 3.33/0.99  --res_prop_simpl_given                  true
% 3.33/0.99  --res_passive_queue_type                priority_queues
% 3.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/0.99  --res_passive_queues_freq               [15;5]
% 3.33/0.99  --res_forward_subs                      full
% 3.33/0.99  --res_backward_subs                     full
% 3.33/0.99  --res_forward_subs_resolution           true
% 3.33/0.99  --res_backward_subs_resolution          true
% 3.33/0.99  --res_orphan_elimination                true
% 3.33/0.99  --res_time_limit                        2.
% 3.33/0.99  --res_out_proof                         true
% 3.33/0.99  
% 3.33/0.99  ------ Superposition Options
% 3.33/0.99  
% 3.33/0.99  --superposition_flag                    true
% 3.33/0.99  --sup_passive_queue_type                priority_queues
% 3.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.33/0.99  --demod_completeness_check              fast
% 3.33/0.99  --demod_use_ground                      true
% 3.33/0.99  --sup_to_prop_solver                    passive
% 3.33/0.99  --sup_prop_simpl_new                    true
% 3.33/0.99  --sup_prop_simpl_given                  true
% 3.33/0.99  --sup_fun_splitting                     false
% 3.33/0.99  --sup_smt_interval                      50000
% 3.33/0.99  
% 3.33/0.99  ------ Superposition Simplification Setup
% 3.33/0.99  
% 3.33/0.99  --sup_indices_passive                   []
% 3.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.99  --sup_full_bw                           [BwDemod]
% 3.33/0.99  --sup_immed_triv                        [TrivRules]
% 3.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.99  --sup_immed_bw_main                     []
% 3.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.99  
% 3.33/0.99  ------ Combination Options
% 3.33/0.99  
% 3.33/0.99  --comb_res_mult                         3
% 3.33/0.99  --comb_sup_mult                         2
% 3.33/0.99  --comb_inst_mult                        10
% 3.33/0.99  
% 3.33/0.99  ------ Debug Options
% 3.33/0.99  
% 3.33/0.99  --dbg_backtrace                         false
% 3.33/0.99  --dbg_dump_prop_clauses                 false
% 3.33/0.99  --dbg_dump_prop_clauses_file            -
% 3.33/0.99  --dbg_out_stat                          false
% 3.33/0.99  ------ Parsing...
% 3.33/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/0.99  ------ Proving...
% 3.33/0.99  ------ Problem Properties 
% 3.33/0.99  
% 3.33/0.99  
% 3.33/0.99  clauses                                 26
% 3.33/0.99  conjectures                             1
% 3.33/0.99  EPR                                     3
% 3.33/0.99  Horn                                    19
% 3.33/0.99  unary                                   3
% 3.33/0.99  binary                                  4
% 3.33/0.99  lits                                    79
% 3.33/0.99  lits eq                                 10
% 3.33/0.99  fd_pure                                 0
% 3.33/0.99  fd_pseudo                               0
% 3.33/0.99  fd_cond                                 0
% 3.33/0.99  fd_pseudo_cond                          2
% 3.33/0.99  AC symbols                              0
% 3.33/0.99  
% 3.33/0.99  ------ Schedule dynamic 5 is on 
% 3.33/0.99  
% 3.33/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/0.99  
% 3.33/0.99  
% 3.33/0.99  ------ 
% 3.33/0.99  Current options:
% 3.33/0.99  ------ 
% 3.33/0.99  
% 3.33/0.99  ------ Input Options
% 3.33/0.99  
% 3.33/0.99  --out_options                           all
% 3.33/0.99  --tptp_safe_out                         true
% 3.33/0.99  --problem_path                          ""
% 3.33/0.99  --include_path                          ""
% 3.33/0.99  --clausifier                            res/vclausify_rel
% 3.33/0.99  --clausifier_options                    --mode clausify
% 3.33/0.99  --stdin                                 false
% 3.33/0.99  --stats_out                             all
% 3.33/0.99  
% 3.33/0.99  ------ General Options
% 3.33/0.99  
% 3.33/0.99  --fof                                   false
% 3.33/0.99  --time_out_real                         305.
% 3.33/0.99  --time_out_virtual                      -1.
% 3.33/0.99  --symbol_type_check                     false
% 3.33/0.99  --clausify_out                          false
% 3.33/0.99  --sig_cnt_out                           false
% 3.33/0.99  --trig_cnt_out                          false
% 3.33/0.99  --trig_cnt_out_tolerance                1.
% 3.33/0.99  --trig_cnt_out_sk_spl                   false
% 3.33/0.99  --abstr_cl_out                          false
% 3.33/0.99  
% 3.33/0.99  ------ Global Options
% 3.33/0.99  
% 3.33/0.99  --schedule                              default
% 3.33/0.99  --add_important_lit                     false
% 3.33/0.99  --prop_solver_per_cl                    1000
% 3.33/0.99  --min_unsat_core                        false
% 3.33/0.99  --soft_assumptions                      false
% 3.33/0.99  --soft_lemma_size                       3
% 3.33/0.99  --prop_impl_unit_size                   0
% 3.33/0.99  --prop_impl_unit                        []
% 3.33/0.99  --share_sel_clauses                     true
% 3.33/0.99  --reset_solvers                         false
% 3.33/0.99  --bc_imp_inh                            [conj_cone]
% 3.33/0.99  --conj_cone_tolerance                   3.
% 3.33/0.99  --extra_neg_conj                        none
% 3.33/0.99  --large_theory_mode                     true
% 3.33/0.99  --prolific_symb_bound                   200
% 3.33/0.99  --lt_threshold                          2000
% 3.33/0.99  --clause_weak_htbl                      true
% 3.33/0.99  --gc_record_bc_elim                     false
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing Options
% 3.33/0.99  
% 3.33/0.99  --preprocessing_flag                    true
% 3.33/0.99  --time_out_prep_mult                    0.1
% 3.33/0.99  --splitting_mode                        input
% 3.33/0.99  --splitting_grd                         true
% 3.33/0.99  --splitting_cvd                         false
% 3.33/0.99  --splitting_cvd_svl                     false
% 3.33/0.99  --splitting_nvd                         32
% 3.33/0.99  --sub_typing                            true
% 3.33/0.99  --prep_gs_sim                           true
% 3.33/0.99  --prep_unflatten                        true
% 3.33/0.99  --prep_res_sim                          true
% 3.33/0.99  --prep_upred                            true
% 3.33/0.99  --prep_sem_filter                       exhaustive
% 3.33/0.99  --prep_sem_filter_out                   false
% 3.33/0.99  --pred_elim                             true
% 3.33/0.99  --res_sim_input                         true
% 3.33/0.99  --eq_ax_congr_red                       true
% 3.33/0.99  --pure_diseq_elim                       true
% 3.33/0.99  --brand_transform                       false
% 3.33/0.99  --non_eq_to_eq                          false
% 3.33/0.99  --prep_def_merge                        true
% 3.33/0.99  --prep_def_merge_prop_impl              false
% 3.33/0.99  --prep_def_merge_mbd                    true
% 3.33/0.99  --prep_def_merge_tr_red                 false
% 3.33/0.99  --prep_def_merge_tr_cl                  false
% 3.33/0.99  --smt_preprocessing                     true
% 3.33/0.99  --smt_ac_axioms                         fast
% 3.33/0.99  --preprocessed_out                      false
% 3.33/0.99  --preprocessed_stats                    false
% 3.33/0.99  
% 3.33/0.99  ------ Abstraction refinement Options
% 3.33/0.99  
% 3.33/0.99  --abstr_ref                             []
% 3.33/0.99  --abstr_ref_prep                        false
% 3.33/0.99  --abstr_ref_until_sat                   false
% 3.33/0.99  --abstr_ref_sig_restrict                funpre
% 3.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.99  --abstr_ref_under                       []
% 3.33/0.99  
% 3.33/0.99  ------ SAT Options
% 3.33/0.99  
% 3.33/0.99  --sat_mode                              false
% 3.33/0.99  --sat_fm_restart_options                ""
% 3.33/0.99  --sat_gr_def                            false
% 3.33/0.99  --sat_epr_types                         true
% 3.33/0.99  --sat_non_cyclic_types                  false
% 3.33/0.99  --sat_finite_models                     false
% 3.33/0.99  --sat_fm_lemmas                         false
% 3.33/0.99  --sat_fm_prep                           false
% 3.33/0.99  --sat_fm_uc_incr                        true
% 3.33/0.99  --sat_out_model                         small
% 3.33/0.99  --sat_out_clauses                       false
% 3.33/0.99  
% 3.33/0.99  ------ QBF Options
% 3.33/0.99  
% 3.33/0.99  --qbf_mode                              false
% 3.33/0.99  --qbf_elim_univ                         false
% 3.33/0.99  --qbf_dom_inst                          none
% 3.33/0.99  --qbf_dom_pre_inst                      false
% 3.33/0.99  --qbf_sk_in                             false
% 3.33/0.99  --qbf_pred_elim                         true
% 3.33/0.99  --qbf_split                             512
% 3.33/0.99  
% 3.33/0.99  ------ BMC1 Options
% 3.33/0.99  
% 3.33/0.99  --bmc1_incremental                      false
% 3.33/0.99  --bmc1_axioms                           reachable_all
% 3.33/0.99  --bmc1_min_bound                        0
% 3.33/0.99  --bmc1_max_bound                        -1
% 3.33/0.99  --bmc1_max_bound_default                -1
% 3.33/0.99  --bmc1_symbol_reachability              true
% 3.33/0.99  --bmc1_property_lemmas                  false
% 3.33/0.99  --bmc1_k_induction                      false
% 3.33/0.99  --bmc1_non_equiv_states                 false
% 3.33/0.99  --bmc1_deadlock                         false
% 3.33/0.99  --bmc1_ucm                              false
% 3.33/0.99  --bmc1_add_unsat_core                   none
% 3.33/0.99  --bmc1_unsat_core_children              false
% 3.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.99  --bmc1_out_stat                         full
% 3.33/0.99  --bmc1_ground_init                      false
% 3.33/0.99  --bmc1_pre_inst_next_state              false
% 3.33/0.99  --bmc1_pre_inst_state                   false
% 3.33/0.99  --bmc1_pre_inst_reach_state             false
% 3.33/0.99  --bmc1_out_unsat_core                   false
% 3.33/0.99  --bmc1_aig_witness_out                  false
% 3.33/0.99  --bmc1_verbose                          false
% 3.33/0.99  --bmc1_dump_clauses_tptp                false
% 3.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.99  --bmc1_dump_file                        -
% 3.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.99  --bmc1_ucm_extend_mode                  1
% 3.33/1.00  --bmc1_ucm_init_mode                    2
% 3.33/1.00  --bmc1_ucm_cone_mode                    none
% 3.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.00  --bmc1_ucm_relax_model                  4
% 3.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.00  --bmc1_ucm_layered_model                none
% 3.33/1.00  --bmc1_ucm_max_lemma_size               10
% 3.33/1.00  
% 3.33/1.00  ------ AIG Options
% 3.33/1.00  
% 3.33/1.00  --aig_mode                              false
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation Options
% 3.33/1.00  
% 3.33/1.00  --instantiation_flag                    true
% 3.33/1.00  --inst_sos_flag                         false
% 3.33/1.00  --inst_sos_phase                        true
% 3.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.00  --inst_lit_sel_side                     none
% 3.33/1.00  --inst_solver_per_active                1400
% 3.33/1.00  --inst_solver_calls_frac                1.
% 3.33/1.00  --inst_passive_queue_type               priority_queues
% 3.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.00  --inst_passive_queues_freq              [25;2]
% 3.33/1.00  --inst_dismatching                      true
% 3.33/1.00  --inst_eager_unprocessed_to_passive     true
% 3.33/1.00  --inst_prop_sim_given                   true
% 3.33/1.00  --inst_prop_sim_new                     false
% 3.33/1.00  --inst_subs_new                         false
% 3.33/1.00  --inst_eq_res_simp                      false
% 3.33/1.00  --inst_subs_given                       false
% 3.33/1.00  --inst_orphan_elimination               true
% 3.33/1.00  --inst_learning_loop_flag               true
% 3.33/1.00  --inst_learning_start                   3000
% 3.33/1.00  --inst_learning_factor                  2
% 3.33/1.00  --inst_start_prop_sim_after_learn       3
% 3.33/1.00  --inst_sel_renew                        solver
% 3.33/1.00  --inst_lit_activity_flag                true
% 3.33/1.00  --inst_restr_to_given                   false
% 3.33/1.00  --inst_activity_threshold               500
% 3.33/1.00  --inst_out_proof                        true
% 3.33/1.00  
% 3.33/1.00  ------ Resolution Options
% 3.33/1.00  
% 3.33/1.00  --resolution_flag                       false
% 3.33/1.00  --res_lit_sel                           adaptive
% 3.33/1.00  --res_lit_sel_side                      none
% 3.33/1.00  --res_ordering                          kbo
% 3.33/1.00  --res_to_prop_solver                    active
% 3.33/1.00  --res_prop_simpl_new                    false
% 3.33/1.00  --res_prop_simpl_given                  true
% 3.33/1.00  --res_passive_queue_type                priority_queues
% 3.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.00  --res_passive_queues_freq               [15;5]
% 3.33/1.00  --res_forward_subs                      full
% 3.33/1.00  --res_backward_subs                     full
% 3.33/1.00  --res_forward_subs_resolution           true
% 3.33/1.00  --res_backward_subs_resolution          true
% 3.33/1.00  --res_orphan_elimination                true
% 3.33/1.00  --res_time_limit                        2.
% 3.33/1.00  --res_out_proof                         true
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Options
% 3.33/1.00  
% 3.33/1.00  --superposition_flag                    true
% 3.33/1.00  --sup_passive_queue_type                priority_queues
% 3.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.00  --demod_completeness_check              fast
% 3.33/1.00  --demod_use_ground                      true
% 3.33/1.00  --sup_to_prop_solver                    passive
% 3.33/1.00  --sup_prop_simpl_new                    true
% 3.33/1.00  --sup_prop_simpl_given                  true
% 3.33/1.00  --sup_fun_splitting                     false
% 3.33/1.00  --sup_smt_interval                      50000
% 3.33/1.00  
% 3.33/1.00  ------ Superposition Simplification Setup
% 3.33/1.00  
% 3.33/1.00  --sup_indices_passive                   []
% 3.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_full_bw                           [BwDemod]
% 3.33/1.00  --sup_immed_triv                        [TrivRules]
% 3.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_immed_bw_main                     []
% 3.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.00  
% 3.33/1.00  ------ Combination Options
% 3.33/1.00  
% 3.33/1.00  --comb_res_mult                         3
% 3.33/1.00  --comb_sup_mult                         2
% 3.33/1.00  --comb_inst_mult                        10
% 3.33/1.00  
% 3.33/1.00  ------ Debug Options
% 3.33/1.00  
% 3.33/1.00  --dbg_backtrace                         false
% 3.33/1.00  --dbg_dump_prop_clauses                 false
% 3.33/1.00  --dbg_dump_prop_clauses_file            -
% 3.33/1.00  --dbg_out_stat                          false
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  ------ Proving...
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS status Theorem for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  fof(f8,axiom,(
% 3.33/1.00    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f19,plain,(
% 3.33/1.00    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.33/1.00    inference(ennf_transformation,[],[f8])).
% 3.33/1.00  
% 3.33/1.00  fof(f20,plain,(
% 3.33/1.00    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.33/1.00    inference(flattening,[],[f19])).
% 3.33/1.00  
% 3.33/1.00  fof(f66,plain,(
% 3.33/1.00    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f20])).
% 3.33/1.00  
% 3.33/1.00  fof(f7,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f24,plain,(
% 3.33/1.00    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 3.33/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.33/1.00  
% 3.33/1.00  fof(f25,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.33/1.00    inference(definition_folding,[],[f7,f24])).
% 3.33/1.00  
% 3.33/1.00  fof(f38,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 3.33/1.00    inference(nnf_transformation,[],[f25])).
% 3.33/1.00  
% 3.33/1.00  fof(f64,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 3.33/1.00    inference(cnf_transformation,[],[f38])).
% 3.33/1.00  
% 3.33/1.00  fof(f77,plain,(
% 3.33/1.00    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 3.33/1.00    inference(equality_resolution,[],[f64])).
% 3.33/1.00  
% 3.33/1.00  fof(f2,axiom,(
% 3.33/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f30,plain,(
% 3.33/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/1.00    inference(nnf_transformation,[],[f2])).
% 3.33/1.00  
% 3.33/1.00  fof(f31,plain,(
% 3.33/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/1.00    inference(flattening,[],[f30])).
% 3.33/1.00  
% 3.33/1.00  fof(f43,plain,(
% 3.33/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.33/1.00    inference(cnf_transformation,[],[f31])).
% 3.33/1.00  
% 3.33/1.00  fof(f73,plain,(
% 3.33/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.33/1.00    inference(equality_resolution,[],[f43])).
% 3.33/1.00  
% 3.33/1.00  fof(f10,conjecture,(
% 3.33/1.00    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f11,negated_conjecture,(
% 3.33/1.00    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.33/1.00    inference(negated_conjecture,[],[f10])).
% 3.33/1.00  
% 3.33/1.00  fof(f23,plain,(
% 3.33/1.00    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 3.33/1.00    inference(ennf_transformation,[],[f11])).
% 3.33/1.00  
% 3.33/1.00  fof(f39,plain,(
% 3.33/1.00    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7)) & r2_hidden(sK7,k1_funct_2(sK5,sK6)))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f40,plain,(
% 3.33/1.00    (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7)) & r2_hidden(sK7,k1_funct_2(sK5,sK6))),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f23,f39])).
% 3.33/1.00  
% 3.33/1.00  fof(f70,plain,(
% 3.33/1.00    r2_hidden(sK7,k1_funct_2(sK5,sK6))),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f32,plain,(
% 3.33/1.00    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.33/1.00    inference(nnf_transformation,[],[f24])).
% 3.33/1.00  
% 3.33/1.00  fof(f33,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.33/1.00    inference(rectify,[],[f32])).
% 3.33/1.00  
% 3.33/1.00  fof(f36,plain,(
% 3.33/1.00    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) & k1_relat_1(sK4(X0,X1,X6)) = X1 & sK4(X0,X1,X6) = X6 & v1_funct_1(sK4(X0,X1,X6)) & v1_relat_1(sK4(X0,X1,X6))))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f35,plain,(
% 3.33/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0) & k1_relat_1(sK3(X0,X1,X2)) = X1 & sK3(X0,X1,X2) = X3 & v1_funct_1(sK3(X0,X1,X2)) & v1_relat_1(sK3(X0,X1,X2))))) )),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f34,plain,(
% 3.33/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK2(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK2(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f37,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK2(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK3(X0,X1,X2)),X0) & k1_relat_1(sK3(X0,X1,X2)) = X1 & sK2(X0,X1,X2) = sK3(X0,X1,X2) & v1_funct_1(sK3(X0,X1,X2)) & v1_relat_1(sK3(X0,X1,X2))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) & k1_relat_1(sK4(X0,X1,X6)) = X1 & sK4(X0,X1,X6) = X6 & v1_funct_1(sK4(X0,X1,X6)) & v1_relat_1(sK4(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f36,f35,f34])).
% 3.33/1.00  
% 3.33/1.00  fof(f55,plain,(
% 3.33/1.00    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK4(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f54,plain,(
% 3.33/1.00    ( ! [X6,X2,X0,X1] : (sK4(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f57,plain,(
% 3.33/1.00    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP0(X0,X1,X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f75,plain,(
% 3.33/1.00    ( ! [X6,X2,X0,X7] : (r2_hidden(X6,X2) | ~r1_tarski(k2_relat_1(X7),X0) | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP0(X0,k1_relat_1(X7),X2)) )),
% 3.33/1.00    inference(equality_resolution,[],[f57])).
% 3.33/1.00  
% 3.33/1.00  fof(f76,plain,(
% 3.33/1.00    ( ! [X2,X0,X7] : (r2_hidden(X7,X2) | ~r1_tarski(k2_relat_1(X7),X0) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | ~sP0(X0,k1_relat_1(X7),X2)) )),
% 3.33/1.00    inference(equality_resolution,[],[f75])).
% 3.33/1.00  
% 3.33/1.00  fof(f52,plain,(
% 3.33/1.00    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK4(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f53,plain,(
% 3.33/1.00    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK4(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f1,axiom,(
% 3.33/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f26,plain,(
% 3.33/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.33/1.00    inference(nnf_transformation,[],[f1])).
% 3.33/1.00  
% 3.33/1.00  fof(f27,plain,(
% 3.33/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.33/1.00    inference(rectify,[],[f26])).
% 3.33/1.00  
% 3.33/1.00  fof(f28,plain,(
% 3.33/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.33/1.00    introduced(choice_axiom,[])).
% 3.33/1.00  
% 3.33/1.00  fof(f29,plain,(
% 3.33/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 3.33/1.00  
% 3.33/1.00  fof(f41,plain,(
% 3.33/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f29])).
% 3.33/1.00  
% 3.33/1.00  fof(f56,plain,(
% 3.33/1.00    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK4(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f37])).
% 3.33/1.00  
% 3.33/1.00  fof(f3,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f12,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.33/1.00    inference(ennf_transformation,[],[f3])).
% 3.33/1.00  
% 3.33/1.00  fof(f13,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.33/1.00    inference(flattening,[],[f12])).
% 3.33/1.00  
% 3.33/1.00  fof(f46,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f13])).
% 3.33/1.00  
% 3.33/1.00  fof(f6,axiom,(
% 3.33/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f17,plain,(
% 3.33/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.33/1.00    inference(ennf_transformation,[],[f6])).
% 3.33/1.00  
% 3.33/1.00  fof(f18,plain,(
% 3.33/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.33/1.00    inference(flattening,[],[f17])).
% 3.33/1.00  
% 3.33/1.00  fof(f51,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f18])).
% 3.33/1.00  
% 3.33/1.00  fof(f9,axiom,(
% 3.33/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f21,plain,(
% 3.33/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.33/1.00    inference(ennf_transformation,[],[f9])).
% 3.33/1.00  
% 3.33/1.00  fof(f22,plain,(
% 3.33/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.33/1.00    inference(flattening,[],[f21])).
% 3.33/1.00  
% 3.33/1.00  fof(f68,plain,(
% 3.33/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f22])).
% 3.33/1.00  
% 3.33/1.00  fof(f69,plain,(
% 3.33/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f22])).
% 3.33/1.00  
% 3.33/1.00  fof(f4,axiom,(
% 3.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f14,plain,(
% 3.33/1.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(ennf_transformation,[],[f4])).
% 3.33/1.00  
% 3.33/1.00  fof(f15,plain,(
% 3.33/1.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.00    inference(flattening,[],[f14])).
% 3.33/1.00  
% 3.33/1.00  fof(f48,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.00    inference(cnf_transformation,[],[f15])).
% 3.33/1.00  
% 3.33/1.00  fof(f71,plain,(
% 3.33/1.00    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7)),
% 3.33/1.00    inference(cnf_transformation,[],[f40])).
% 3.33/1.00  
% 3.33/1.00  fof(f5,axiom,(
% 3.33/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 3.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/1.00  
% 3.33/1.00  fof(f16,plain,(
% 3.33/1.00    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.33/1.00    inference(ennf_transformation,[],[f5])).
% 3.33/1.00  
% 3.33/1.00  fof(f49,plain,(
% 3.33/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.33/1.00    inference(cnf_transformation,[],[f16])).
% 3.33/1.00  
% 3.33/1.00  cnf(c_25,plain,
% 3.33/1.00      ( ~ v1_xboole_0(X0)
% 3.33/1.00      | v1_xboole_0(X1)
% 3.33/1.00      | v1_xboole_0(k1_funct_2(X1,X0)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7047,plain,
% 3.33/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.33/1.00      | v1_xboole_0(X1) = iProver_top
% 3.33/1.00      | v1_xboole_0(k1_funct_2(X1,X0)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_24,plain,
% 3.33/1.00      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7048,plain,
% 3.33/1.00      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_4,plain,
% 3.33/1.00      ( r1_tarski(X0,X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7063,plain,
% 3.33/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_30,negated_conjecture,
% 3.33/1.00      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7045,plain,
% 3.33/1.00      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_19,plain,
% 3.33/1.00      ( ~ sP0(X0,X1,X2)
% 3.33/1.00      | ~ r2_hidden(X3,X2)
% 3.33/1.00      | k1_relat_1(sK4(X0,X1,X3)) = X1 ),
% 3.33/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7053,plain,
% 3.33/1.00      ( k1_relat_1(sK4(X0,X1,X2)) = X1
% 3.33/1.00      | sP0(X0,X1,X3) != iProver_top
% 3.33/1.00      | r2_hidden(X2,X3) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8031,plain,
% 3.33/1.00      ( k1_relat_1(sK4(X0,X1,X2)) = X1
% 3.33/1.00      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7048,c_7053]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8365,plain,
% 3.33/1.00      ( k1_relat_1(sK4(sK6,sK5,sK7)) = sK5 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7045,c_8031]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_20,plain,
% 3.33/1.00      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK4(X0,X1,X3) = X3 ),
% 3.33/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7052,plain,
% 3.33/1.00      ( sK4(X0,X1,X2) = X2
% 3.33/1.00      | sP0(X0,X1,X3) != iProver_top
% 3.33/1.00      | r2_hidden(X2,X3) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7785,plain,
% 3.33/1.00      ( sK4(X0,X1,X2) = X2
% 3.33/1.00      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7048,c_7052]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7869,plain,
% 3.33/1.00      ( sK4(sK6,sK5,sK7) = sK7 ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7045,c_7785]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8367,plain,
% 3.33/1.00      ( k1_relat_1(sK7) = sK5 ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_8365,c_7869]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_17,plain,
% 3.33/1.00      ( ~ sP0(X0,k1_relat_1(X1),X2)
% 3.33/1.00      | ~ r1_tarski(k2_relat_1(X1),X0)
% 3.33/1.00      | r2_hidden(X1,X2)
% 3.33/1.00      | ~ v1_funct_1(X1)
% 3.33/1.00      | ~ v1_relat_1(X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7055,plain,
% 3.33/1.00      ( sP0(X0,k1_relat_1(X1),X2) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 3.33/1.00      | r2_hidden(X1,X2) = iProver_top
% 3.33/1.00      | v1_funct_1(X1) != iProver_top
% 3.33/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9882,plain,
% 3.33/1.00      ( sP0(X0,sK5,X1) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(sK7),X0) != iProver_top
% 3.33/1.00      | r2_hidden(sK7,X1) = iProver_top
% 3.33/1.00      | v1_funct_1(sK7) != iProver_top
% 3.33/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_8367,c_7055]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_22,plain,
% 3.33/1.00      ( ~ sP0(X0,X1,X2)
% 3.33/1.00      | ~ r2_hidden(X3,X2)
% 3.33/1.00      | v1_relat_1(sK4(X0,X1,X3)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7050,plain,
% 3.33/1.00      ( sP0(X0,X1,X2) != iProver_top
% 3.33/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.33/1.00      | v1_relat_1(sK4(X0,X1,X3)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7993,plain,
% 3.33/1.00      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.33/1.00      | v1_relat_1(sK4(X2,X1,X0)) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7048,c_7050]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8137,plain,
% 3.33/1.00      ( v1_relat_1(sK4(sK6,sK5,sK7)) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7045,c_7993]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8139,plain,
% 3.33/1.00      ( v1_relat_1(sK7) = iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_8137,c_7869]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_21,plain,
% 3.33/1.00      ( ~ sP0(X0,X1,X2)
% 3.33/1.00      | ~ r2_hidden(X3,X2)
% 3.33/1.00      | v1_funct_1(sK4(X0,X1,X3)) ),
% 3.33/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7051,plain,
% 3.33/1.00      ( sP0(X0,X1,X2) != iProver_top
% 3.33/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.33/1.00      | v1_funct_1(sK4(X0,X1,X3)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7999,plain,
% 3.33/1.00      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 3.33/1.00      | v1_funct_1(sK4(X2,X1,X0)) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7048,c_7051]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8265,plain,
% 3.33/1.00      ( v1_funct_1(sK4(sK6,sK5,sK7)) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7045,c_7999]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8267,plain,
% 3.33/1.00      ( v1_funct_1(sK7) = iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_8265,c_7869]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10402,plain,
% 3.33/1.00      ( sP0(X0,sK5,X1) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(sK7),X0) != iProver_top
% 3.33/1.00      | r2_hidden(sK7,X1) = iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_9882,c_8139,c_8267]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10411,plain,
% 3.33/1.00      ( sP0(k2_relat_1(sK7),sK5,X0) != iProver_top
% 3.33/1.00      | r2_hidden(sK7,X0) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7063,c_10402]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10662,plain,
% 3.33/1.00      ( r2_hidden(sK7,k1_funct_2(sK5,k2_relat_1(sK7))) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7048,c_10411]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_1,plain,
% 3.33/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7065,plain,
% 3.33/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.33/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10666,plain,
% 3.33/1.00      ( v1_xboole_0(k1_funct_2(sK5,k2_relat_1(sK7))) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_10662,c_7065]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_10782,plain,
% 3.33/1.00      ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top
% 3.33/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7047,c_10666]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_18,plain,
% 3.33/1.00      ( ~ sP0(X0,X1,X2)
% 3.33/1.00      | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0)
% 3.33/1.00      | ~ r2_hidden(X3,X2) ),
% 3.33/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7054,plain,
% 3.33/1.00      ( sP0(X0,X1,X2) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(sK4(X0,X1,X3)),X0) = iProver_top
% 3.33/1.00      | r2_hidden(X3,X2) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8776,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) = iProver_top
% 3.33/1.00      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7048,c_7054]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9613,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top
% 3.33/1.00      | r2_hidden(sK7,k1_funct_2(sK5,sK6)) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7869,c_8776]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_5,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.33/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.33/1.00      | ~ v1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7062,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.33/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9,plain,
% 3.33/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.33/1.00      | v1_partfun1(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | v1_xboole_0(X2) ),
% 3.33/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_27,plain,
% 3.33/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_381,plain,
% 3.33/1.00      ( v1_partfun1(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v1_funct_1(X3)
% 3.33/1.00      | ~ v1_relat_1(X3)
% 3.33/1.00      | v1_xboole_0(X2)
% 3.33/1.00      | X3 != X0
% 3.33/1.00      | k1_relat_1(X3) != X1
% 3.33/1.00      | k2_relat_1(X3) != X2 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_382,plain,
% 3.33/1.00      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | v1_xboole_0(k2_relat_1(X0)) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_381]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_26,plain,
% 3.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v1_relat_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_386,plain,
% 3.33/1.00      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | v1_xboole_0(k2_relat_1(X0)) ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_382,c_26]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6,plain,
% 3.33/1.00      ( v1_funct_2(X0,X1,X2)
% 3.33/1.00      | ~ v1_partfun1(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ v1_funct_1(X0) ),
% 3.33/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_29,negated_conjecture,
% 3.33/1.00      ( ~ v1_funct_2(sK7,sK5,sK6)
% 3.33/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.33/1.00      | ~ v1_funct_1(sK7) ),
% 3.33/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_405,plain,
% 3.33/1.00      ( ~ v1_partfun1(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v1_funct_1(sK7)
% 3.33/1.00      | sK6 != X2
% 3.33/1.00      | sK5 != X1
% 3.33/1.00      | sK7 != X0 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_406,plain,
% 3.33/1.00      ( ~ v1_partfun1(sK7,sK5)
% 3.33/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.33/1.00      | ~ v1_funct_1(sK7) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_405]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_470,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.33/1.00      | ~ v1_funct_1(X0)
% 3.33/1.00      | ~ v1_funct_1(sK7)
% 3.33/1.00      | ~ v1_relat_1(X0)
% 3.33/1.00      | v1_xboole_0(k2_relat_1(X0))
% 3.33/1.00      | k1_relat_1(X0) != sK5
% 3.33/1.00      | sK7 != X0 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_386,c_406]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_471,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.33/1.00      | ~ v1_funct_1(sK7)
% 3.33/1.00      | ~ v1_relat_1(sK7)
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7))
% 3.33/1.00      | k1_relat_1(sK7) != sK5 ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_470]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7041,plain,
% 3.33/1.00      ( k1_relat_1(sK7) != sK5
% 3.33/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.33/1.00      | v1_funct_1(sK7) != iProver_top
% 3.33/1.00      | v1_relat_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8576,plain,
% 3.33/1.00      ( sK5 != sK5
% 3.33/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.33/1.00      | v1_funct_1(sK7) != iProver_top
% 3.33/1.00      | v1_relat_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(demodulation,[status(thm)],[c_8367,c_7041]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8587,plain,
% 3.33/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.33/1.00      | v1_funct_1(sK7) != iProver_top
% 3.33/1.00      | v1_relat_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(equality_resolution_simp,[status(thm)],[c_8576]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_472,plain,
% 3.33/1.00      ( k1_relat_1(sK7) != sK5
% 3.33/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.33/1.00      | v1_funct_1(sK7) != iProver_top
% 3.33/1.00      | v1_relat_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9521,plain,
% 3.33/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_8587,c_472,c_8139,c_8267,c_8367]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9527,plain,
% 3.33/1.00      ( r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.33/1.00      | v1_relat_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7062,c_9521]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9528,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.33/1.00      | r1_tarski(sK5,sK5) != iProver_top
% 3.33/1.00      | v1_relat_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_9527,c_8367]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9531,plain,
% 3.33/1.00      ( r1_tarski(sK5,sK5) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_9528,c_8139]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9532,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.33/1.00      | r1_tarski(sK5,sK5) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(renaming,[status(thm)],[c_9531]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9538,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.33/1.00      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 3.33/1.00      inference(forward_subsumption_resolution,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_9532,c_7063]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_8,plain,
% 3.33/1.00      ( v1_partfun1(X0,X1)
% 3.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ v1_xboole_0(X1) ),
% 3.33/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_452,plain,
% 3.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.33/1.00      | ~ v1_funct_1(sK7)
% 3.33/1.00      | ~ v1_xboole_0(X1)
% 3.33/1.00      | sK5 != X1
% 3.33/1.00      | sK7 != X0 ),
% 3.33/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_406]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_453,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
% 3.33/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.33/1.00      | ~ v1_funct_1(sK7)
% 3.33/1.00      | ~ v1_xboole_0(sK5) ),
% 3.33/1.00      inference(unflattening,[status(thm)],[c_452]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6544,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.33/1.00      | ~ v1_funct_1(sK7)
% 3.33/1.00      | ~ v1_xboole_0(sK5)
% 3.33/1.00      | sP0_iProver_split ),
% 3.33/1.00      inference(splitting,
% 3.33/1.00                [splitting(split),new_symbols(definition,[])],
% 3.33/1.00                [c_453]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7042,plain,
% 3.33/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.33/1.00      | v1_funct_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(sK5) != iProver_top
% 3.33/1.00      | sP0_iProver_split = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_6544]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_6543,plain,
% 3.33/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
% 3.33/1.00      | ~ sP0_iProver_split ),
% 3.33/1.00      inference(splitting,
% 3.33/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.33/1.00                [c_453]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7043,plain,
% 3.33/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) != iProver_top
% 3.33/1.00      | sP0_iProver_split != iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_6543]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_7159,plain,
% 3.33/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.33/1.00      | v1_funct_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.33/1.00      inference(forward_subsumption_resolution,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_7042,c_7043]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9189,plain,
% 3.33/1.00      ( r1_tarski(k1_relat_1(sK7),sK5) != iProver_top
% 3.33/1.00      | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.33/1.00      | v1_funct_1(sK7) != iProver_top
% 3.33/1.00      | v1_relat_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.33/1.00      inference(superposition,[status(thm)],[c_7062,c_7159]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9196,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.33/1.00      | r1_tarski(sK5,sK5) != iProver_top
% 3.33/1.00      | v1_funct_1(sK7) != iProver_top
% 3.33/1.00      | v1_relat_1(sK7) != iProver_top
% 3.33/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.33/1.00      inference(light_normalisation,[status(thm)],[c_9189,c_8367]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9351,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.33/1.00      | r1_tarski(sK5,sK5) != iProver_top
% 3.33/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.33/1.00      inference(global_propositional_subsumption,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_9196,c_8139,c_8267]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_9358,plain,
% 3.33/1.00      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 3.33/1.00      | v1_xboole_0(sK5) != iProver_top ),
% 3.33/1.00      inference(forward_subsumption_resolution,
% 3.33/1.00                [status(thm)],
% 3.33/1.00                [c_9351,c_7063]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(c_31,plain,
% 3.33/1.00      ( r2_hidden(sK7,k1_funct_2(sK5,sK6)) = iProver_top ),
% 3.33/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.00  
% 3.33/1.00  cnf(contradiction,plain,
% 3.33/1.00      ( $false ),
% 3.33/1.00      inference(minisat,[status(thm)],[c_10782,c_9613,c_9538,c_9358,c_31]) ).
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.00  
% 3.33/1.00  ------                               Statistics
% 3.33/1.00  
% 3.33/1.00  ------ General
% 3.33/1.00  
% 3.33/1.00  abstr_ref_over_cycles:                  0
% 3.33/1.00  abstr_ref_under_cycles:                 0
% 3.33/1.00  gc_basic_clause_elim:                   0
% 3.33/1.00  forced_gc_time:                         0
% 3.33/1.00  parsing_time:                           0.011
% 3.33/1.00  unif_index_cands_time:                  0.
% 3.33/1.00  unif_index_add_time:                    0.
% 3.33/1.00  orderings_time:                         0.
% 3.33/1.00  out_proof_time:                         0.011
% 3.33/1.00  total_time:                             0.233
% 3.33/1.00  num_of_symbols:                         53
% 3.33/1.00  num_of_terms:                           6017
% 3.33/1.00  
% 3.33/1.00  ------ Preprocessing
% 3.33/1.00  
% 3.33/1.00  num_of_splits:                          1
% 3.33/1.00  num_of_split_atoms:                     1
% 3.33/1.00  num_of_reused_defs:                     0
% 3.33/1.00  num_eq_ax_congr_red:                    35
% 3.33/1.00  num_of_sem_filtered_clauses:            1
% 3.33/1.00  num_of_subtypes:                        0
% 3.33/1.00  monotx_restored_types:                  0
% 3.33/1.00  sat_num_of_epr_types:                   0
% 3.33/1.00  sat_num_of_non_cyclic_types:            0
% 3.33/1.00  sat_guarded_non_collapsed_types:        0
% 3.33/1.00  num_pure_diseq_elim:                    0
% 3.33/1.00  simp_replaced_by:                       0
% 3.33/1.00  res_preprocessed:                       135
% 3.33/1.00  prep_upred:                             0
% 3.33/1.00  prep_unflattend:                        356
% 3.33/1.00  smt_new_axioms:                         0
% 3.33/1.00  pred_elim_cands:                        7
% 3.33/1.00  pred_elim:                              2
% 3.33/1.00  pred_elim_cl:                           2
% 3.33/1.00  pred_elim_cycles:                       11
% 3.33/1.00  merged_defs:                            0
% 3.33/1.00  merged_defs_ncl:                        0
% 3.33/1.00  bin_hyper_res:                          0
% 3.33/1.00  prep_cycles:                            4
% 3.33/1.00  pred_elim_time:                         0.09
% 3.33/1.00  splitting_time:                         0.
% 3.33/1.00  sem_filter_time:                        0.
% 3.33/1.00  monotx_time:                            0.
% 3.33/1.00  subtype_inf_time:                       0.
% 3.33/1.00  
% 3.33/1.00  ------ Problem properties
% 3.33/1.00  
% 3.33/1.00  clauses:                                26
% 3.33/1.00  conjectures:                            1
% 3.33/1.00  epr:                                    3
% 3.33/1.00  horn:                                   19
% 3.33/1.00  ground:                                 4
% 3.33/1.00  unary:                                  3
% 3.33/1.00  binary:                                 4
% 3.33/1.00  lits:                                   79
% 3.33/1.00  lits_eq:                                10
% 3.33/1.00  fd_pure:                                0
% 3.33/1.00  fd_pseudo:                              0
% 3.33/1.00  fd_cond:                                0
% 3.33/1.00  fd_pseudo_cond:                         2
% 3.33/1.00  ac_symbols:                             0
% 3.33/1.00  
% 3.33/1.00  ------ Propositional Solver
% 3.33/1.00  
% 3.33/1.00  prop_solver_calls:                      28
% 3.33/1.00  prop_fast_solver_calls:                 2292
% 3.33/1.00  smt_solver_calls:                       0
% 3.33/1.00  smt_fast_solver_calls:                  0
% 3.33/1.00  prop_num_of_clauses:                    2213
% 3.33/1.00  prop_preprocess_simplified:             7526
% 3.33/1.00  prop_fo_subsumed:                       38
% 3.33/1.00  prop_solver_time:                       0.
% 3.33/1.00  smt_solver_time:                        0.
% 3.33/1.00  smt_fast_solver_time:                   0.
% 3.33/1.00  prop_fast_solver_time:                  0.
% 3.33/1.00  prop_unsat_core_time:                   0.
% 3.33/1.00  
% 3.33/1.00  ------ QBF
% 3.33/1.00  
% 3.33/1.00  qbf_q_res:                              0
% 3.33/1.00  qbf_num_tautologies:                    0
% 3.33/1.00  qbf_prep_cycles:                        0
% 3.33/1.00  
% 3.33/1.00  ------ BMC1
% 3.33/1.00  
% 3.33/1.00  bmc1_current_bound:                     -1
% 3.33/1.00  bmc1_last_solved_bound:                 -1
% 3.33/1.00  bmc1_unsat_core_size:                   -1
% 3.33/1.00  bmc1_unsat_core_parents_size:           -1
% 3.33/1.00  bmc1_merge_next_fun:                    0
% 3.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.33/1.00  
% 3.33/1.00  ------ Instantiation
% 3.33/1.00  
% 3.33/1.00  inst_num_of_clauses:                    493
% 3.33/1.00  inst_num_in_passive:                    137
% 3.33/1.00  inst_num_in_active:                     224
% 3.33/1.00  inst_num_in_unprocessed:                132
% 3.33/1.00  inst_num_of_loops:                      280
% 3.33/1.00  inst_num_of_learning_restarts:          0
% 3.33/1.00  inst_num_moves_active_passive:          52
% 3.33/1.00  inst_lit_activity:                      0
% 3.33/1.00  inst_lit_activity_moves:                0
% 3.33/1.00  inst_num_tautologies:                   0
% 3.33/1.00  inst_num_prop_implied:                  0
% 3.33/1.00  inst_num_existing_simplified:           0
% 3.33/1.00  inst_num_eq_res_simplified:             0
% 3.33/1.00  inst_num_child_elim:                    0
% 3.33/1.00  inst_num_of_dismatching_blockings:      353
% 3.33/1.00  inst_num_of_non_proper_insts:           373
% 3.33/1.00  inst_num_of_duplicates:                 0
% 3.33/1.00  inst_inst_num_from_inst_to_res:         0
% 3.33/1.00  inst_dismatching_checking_time:         0.
% 3.33/1.00  
% 3.33/1.00  ------ Resolution
% 3.33/1.00  
% 3.33/1.00  res_num_of_clauses:                     0
% 3.33/1.00  res_num_in_passive:                     0
% 3.33/1.00  res_num_in_active:                      0
% 3.33/1.00  res_num_of_loops:                       139
% 3.33/1.00  res_forward_subset_subsumed:            8
% 3.33/1.00  res_backward_subset_subsumed:           0
% 3.33/1.00  res_forward_subsumed:                   0
% 3.33/1.00  res_backward_subsumed:                  0
% 3.33/1.00  res_forward_subsumption_resolution:     2
% 3.33/1.00  res_backward_subsumption_resolution:    0
% 3.33/1.00  res_clause_to_clause_subsumption:       572
% 3.33/1.00  res_orphan_elimination:                 0
% 3.33/1.00  res_tautology_del:                      26
% 3.33/1.00  res_num_eq_res_simplified:              0
% 3.33/1.00  res_num_sel_changes:                    0
% 3.33/1.00  res_moves_from_active_to_pass:          0
% 3.33/1.00  
% 3.33/1.00  ------ Superposition
% 3.33/1.00  
% 3.33/1.00  sup_time_total:                         0.
% 3.33/1.00  sup_time_generating:                    0.
% 3.33/1.00  sup_time_sim_full:                      0.
% 3.33/1.00  sup_time_sim_immed:                     0.
% 3.33/1.00  
% 3.33/1.00  sup_num_of_clauses:                     88
% 3.33/1.00  sup_num_in_active:                      54
% 3.33/1.00  sup_num_in_passive:                     34
% 3.33/1.00  sup_num_of_loops:                       55
% 3.33/1.00  sup_fw_superposition:                   33
% 3.33/1.00  sup_bw_superposition:                   35
% 3.33/1.00  sup_immediate_simplified:               14
% 3.33/1.00  sup_given_eliminated:                   0
% 3.33/1.00  comparisons_done:                       0
% 3.33/1.00  comparisons_avoided:                    0
% 3.33/1.00  
% 3.33/1.00  ------ Simplifications
% 3.33/1.00  
% 3.33/1.00  
% 3.33/1.00  sim_fw_subset_subsumed:                 1
% 3.33/1.00  sim_bw_subset_subsumed:                 0
% 3.33/1.00  sim_fw_subsumed:                        4
% 3.33/1.00  sim_bw_subsumed:                        0
% 3.33/1.00  sim_fw_subsumption_res:                 3
% 3.33/1.00  sim_bw_subsumption_res:                 0
% 3.33/1.00  sim_tautology_del:                      1
% 3.33/1.00  sim_eq_tautology_del:                   2
% 3.33/1.00  sim_eq_res_simp:                        2
% 3.33/1.00  sim_fw_demodulated:                     0
% 3.33/1.00  sim_bw_demodulated:                     2
% 3.33/1.00  sim_light_normalised:                   9
% 3.33/1.00  sim_joinable_taut:                      0
% 3.33/1.00  sim_joinable_simp:                      0
% 3.33/1.00  sim_ac_normalised:                      0
% 3.33/1.00  sim_smt_subsumption:                    0
% 3.33/1.00  
%------------------------------------------------------------------------------
